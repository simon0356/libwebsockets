/*
 * lws-minimal-http-client
 *
 * Written in 2010-2021 by Andy Green <andy@warmcat.com>
 *
 * This file is made available under the Creative Commons CC0 1.0
 * Universal Public Domain Dedication.
 *
 * This demonstrates the a minimal http client using lws.
 *
 * It visits https://warmcat.com/ and receives the html page there.  You
 * can dump the page data by changing the #if 0 below.
 */

#include <libwebsockets.h>
#include <openssl/rand.h>
#include <string.h>
#include <signal.h>
#include <stdbool.h>
#include <openssl/md5.h>
#include <stdint.h>
static int interrupted, bad = 1, status, conmon, close_after_start;
#if defined(LWS_WITH_HTTP2)
static int long_poll;
#endif
static struct lws *client_wsi;
static const char *ba_user, *ba_password;

static const lws_retry_bo_t retry = {
	.secs_since_valid_ping = 3,
	.secs_since_valid_hangup = 10,
};

#if defined(LWS_WITH_CONMON)
void
dump_conmon_data(struct lws *wsi)
{
	const struct addrinfo *ai;
	struct lws_conmon cm;
	char ads[48];

	lws_conmon_wsi_take(wsi, &cm);

	lws_sa46_write_numeric_address(&cm.peer46, ads, sizeof(ads));
	lwsl_notice("%s: peer %s, dns: %uus, sockconn: %uus, tls: %uus, txn_resp: %uus\n",
		    __func__, ads,
		    (unsigned int)cm.ciu_dns,
		    (unsigned int)cm.ciu_sockconn,
		    (unsigned int)cm.ciu_tls,
		    (unsigned int)cm.ciu_txn_resp);

	ai = cm.dns_results_copy;
	while (ai) {
		lws_sa46_write_numeric_address((lws_sockaddr46 *)ai->ai_addr, ads, sizeof(ads));
		lwsl_notice("%s: DNS %s\n", __func__, ads);
		ai = ai->ai_next;
	}

	/*
	 * This destroys the DNS list in the lws_conmon that we took
	 * responsibility for when we used lws_conmon_wsi_take()
	 */

	lws_conmon_release(&cm);
}
#endif

static const char *ua = "Mozilla/5.0 (X11; Linux x86_64) "
			"AppleWebKit/537.36 (KHTML, like Gecko) "
			"Chrome/51.0.2704.103 Safari/537.36",
		  *acc = "*/*";

#define SESSION_ALGO 1 /* for algos with this bit set */

#define ALGO_MD5 0
#define ALGO_MD5SESS (ALGO_MD5 | SESSION_ALGO)
#define ALGO_SHA256 2
#define ALGO_SHA256SESS (ALGO_SHA256 | SESSION_ALGO)
#define ALGO_SHA512_256 4
#define ALGO_SHA512_256SESS (ALGO_SHA512_256 | SESSION_ALGO)
#define DIGEST_MAX_VALUE_LENGTH           256
#define DIGEST_MAX_CONTENT_LENGTH         1024
#define DIGEST_QOP_VALUE_STRING_AUTH      "auth"
#define DIGEST_QOP_VALUE_STRING_AUTH_INT  "auth-int"
#define DIGEST_QOP_VALUE_STRING_AUTH_CONF "auth-conf"
#define ISBLANK(x)  (((x) == ' ') || ((x) == '\t'))

/* Struct used for Digest challenge-response authentication from libcurl*/
struct digestdata {
  char *nonce;
  char *cnonce;
  char *realm;
  char *opaque;
  char *qop;
  char *algorithm;
  int nc; /* nonce count */
  unsigned char algo;
  bool stale; /* set true for re-negotiation */
  bool userhash;
};

bool Curl_auth_digest_get_pair(const char *str, char *value, char *content,
                               const char **endptr)
{
  int c;
  bool starts_with_quote = false;
  bool escape = false;

  for(c = DIGEST_MAX_VALUE_LENGTH - 1; (*str && (*str != '=') && c--);)
    *value++ = *str++;
  *value = 0;

  if('=' != *str++)
    /* eek, no match */
    return false;

  if('\"' == *str) {
    /* This starts with a quote so it must end with one as well! */
    str++;
    starts_with_quote = true;
  }

  for(c = DIGEST_MAX_CONTENT_LENGTH - 1; *str && c--; str++) {
    if(!escape) {
      switch(*str) {
      case '\\':
        if(starts_with_quote) {
          /* the start of an escaped quote */
          escape = true;
          continue;
        }
        break;

      case ',':
        if(!starts_with_quote) {
          /* This signals the end of the content if we didn't get a starting
             quote and then we do "sloppy" parsing */
          c = 0; /* the end */
          continue;
        }
        break;

      case '\r':
      case '\n':
        /* end of string */
        if(starts_with_quote)
          return false; /* No closing quote */
        c = 0;
        continue;

      case '\"':
        if(starts_with_quote) {
          /* end of string */
          c = 0;
          continue;
        }
        else
          return false;
        break;
      }
    }

    escape = false;
    *content++ = *str;
  }
  if(escape)
    return false; /* No character after backslash */

  *content = 0;
  *endptr = str;

  return true;
}

/*
 * Curl_auth_digest_cleanup()
 *
 * This is used to clean up the digest specific data.
 *
 * Parameters:
 *
 * digest    [in/out] - The digest data struct being cleaned up.
 *
 */
void Curl_auth_digest_cleanup(struct digestdata *digest)
{
  if(digest->nonce)
    free(digest->nonce);
  if(digest->cnonce)
    free(digest->cnonce);
  if(digest->realm)
    free(digest->realm);
  if(digest->opaque)
    free(digest->opaque);
  if(digest->qop)
    free(digest->qop);
  if(digest->algorithm)
    free(digest->algorithm);

  digest->nc = 0;
  digest->algo = ALGO_MD5; /* default algorithm */
  digest->stale = false; /* default means normal, not stale */
  digest->userhash = false;
}

/*
 * Curl_auth_decode_digest_http_message()
 *
 * This is used to decode an HTTP DIGEST challenge message into the separate
 * attributes.
 *
 * Parameters:
 *
 * chlg    [in]     - The challenge message.
 * digest  [in/out] - The digest data struct being used and modified.
 *
 * Returns CURLE_OK on success.
 */
int auth_decode_digest_http_message(const char *chlg,
                                              struct digestdata *digest)
{
  bool before = false; /* got a nonce before */
  bool foundAuth = false;
  bool foundAuthInt = false;
  char *token = NULL;
  char *tmp = NULL;

  /* If we already have received a nonce, keep that in mind */
  if(digest->nonce)
    before = true;

  /* Clean up any former leftovers and initialise to defaults */
  Curl_auth_digest_cleanup(digest);

  for(;;) {
    char value[DIGEST_MAX_VALUE_LENGTH];
    char content[DIGEST_MAX_CONTENT_LENGTH];

    /* Pass all additional spaces here */
    while(*chlg && ISBLANK(*chlg))
      chlg++;

    /* Extract a value=content pair */
    if(Curl_auth_digest_get_pair(chlg, value, content, &chlg)) {
      if(strcasecmp(value, "nonce") == 0) {
        free(digest->nonce);
        digest->nonce = strdup(content);
        if(!digest->nonce)
          return -1;
      }
      else if(strcasecmp(value, "stale") == 0) {
        if(strcasecmp(content, "true") == 0) {
          digest->stale = true;
          digest->nc = 1; /* we make a new nonce now */
        }
      }
      else if(strcasecmp(value, "realm") == 0) {
        free(digest->realm);
        digest->realm = strdup(content);
        if(!digest->realm)
          return -1;
      }
      else if(strcasecmp(value, "opaque") == 0) {
        free(digest->opaque);
        digest->opaque = strdup(content);
        if(!digest->opaque)
          return -1;
      }
      else if(strcasecmp(value, "qop") == 0) {
        char *tok_buf = NULL;
        /* Tokenize the list and choose auth if possible, use a temporary
           clone of the buffer since strtok_r() ruins it */
        tmp = strdup(content);
        if(!tmp)
          return -1;

        token = strtok_r(tmp, ",", &tok_buf);
        while(token) {
          /* Pass additional spaces here */
          while(*token && ISBLANK(*token))
            token++;
          if(strcasecmp(token, DIGEST_QOP_VALUE_STRING_AUTH) == 0) {
            foundAuth = true;
          }
          else if(strcasecmp(token, DIGEST_QOP_VALUE_STRING_AUTH_INT) == 0) {
            foundAuthInt = true;
          }
          token = strtok_r(NULL, ",", &tok_buf);
        }

        free(tmp);

        /* Select only auth or auth-int. Otherwise, ignore */
        if(foundAuth) {
          if(digest->qop)
            free(digest->qop);
          digest->qop = strdup(DIGEST_QOP_VALUE_STRING_AUTH);
          if(!digest->qop)
            return -1;
        }
        else if(foundAuthInt) {
          free(digest->qop);
          digest->qop = strdup(DIGEST_QOP_VALUE_STRING_AUTH_INT);
          if(!digest->qop)
            return -1;
        }
      }
      else if(strcasecmp(value, "algorithm") == 0) {
        free(digest->algorithm);
        digest->algorithm = strdup(content);
        if(!digest->algorithm)
          return -1;

        if(strcasecmp(content, "MD5-sess") == 0)
          digest->algo = ALGO_MD5SESS;
        else if(strcasecmp(content, "MD5") == 0)
          digest->algo = ALGO_MD5;
        else if(strcasecmp(content, "SHA-256") == 0)
          digest->algo = ALGO_SHA256;
        else if(strcasecmp(content, "SHA-256-SESS") == 0)
          digest->algo = ALGO_SHA256SESS;
        else if(strcasecmp(content, "SHA-512-256") == 0)
          digest->algo = ALGO_SHA512_256;
        else if(strcasecmp(content, "SHA-512-256-SESS") == 0)
          digest->algo = ALGO_SHA512_256SESS;
        else
          return -1;
      }
      else if(strcasecmp(value, "userhash") == 0) {
        if(strcasecmp(content, "true") == 0) {
          digest->userhash = true;
        }
      }
      else {
        /* Unknown specifier, ignore it! */
      }
    }
    else
      break; /* We're done here */

    /* Pass all additional spaces here */
    while(*chlg && ISBLANK(*chlg))
      chlg++;

    /* Allow the list to be comma-separated */
    if(',' == *chlg)
      chlg++;
  }

  /* We had a nonce since before, and we got another one now without
     'stale=true'. This means we provided bad credentials in the previous
     request */
  if(before && !digest->stale)
    return -1;

  /* We got this header without a nonce, that's a bad Digest line! */
  if(!digest->nonce)
    return -1;

  /* "<algo>-sess" protocol versions require "auth" or "auth-int" qop */
  if(!digest->qop && (digest->algo & SESSION_ALGO))
    return -1;

  return 0;
}

int md5_hash(uint8_t *output, uint8_t* input, size_t len){
  MD5_CTX ctx;
  int result =MD5_Init(&ctx);
  if(!result) {
    MD5_Update(&ctx, input, len);
    MD5_Final(output, &ctx);
  }
  return result;
}
/* Convert md5 chunk to RFC2617 (section 3.1.3) -suitable ascii string */
static void convert_to_ascii(unsigned char *source, /* 16 bytes */
                                     unsigned char *dest) /* 33 bytes */
{
  int i;
  for(i = 0; i < 16; i++)
    snprintf((char *) &dest[i * 2], 3, "%02x", source[i]);
}
/* Perform quoted-string escaping as described in RFC2616 and its errata */
static char *auth_digest_string_quoted(const char *source)
{
  char *dest;
  const char *s = source;
  size_t n = 1; /* null terminator */

  /* Calculate size needed */
  while(*s) {
    ++n;
    if(*s == '"' || *s == '\\') {
      ++n;
    }
    ++s;
  }

  dest = malloc(n);
  if(dest) {
    char *d = dest;
    s = source;
    while(*s) {
      if(*s == '"' || *s == '\\') {
        *d++ = '\\';
      }
      *d++ = *s++;
    }
    *d = '\0';
  }

  return dest;
}
int output_digest(struct lws *wsi, char *http_req,  char *uri, char *user, char *password, char *challenge,
    char **outptr, size_t *outlen
    )
{
  //printf("Calculate Digest response for path %s, user %s password %s and challenge %s\r\n",uri,user,password,challenge);

  unsigned char hashbuf[32]; /* 32 bytes/256 bits */
  unsigned char request_digest[65];
  unsigned char ha1[65];    /* 64 digits and 1 zero byte */
  unsigned char ha2[65];    /* 64 digits and 1 zero byte */
  char userh[65];
  char cnonce[65];
  char *userp_quoted;
  char *realm_quoted;
  char *nonce_quoted;
  char *response = NULL;
  char *hashthis = NULL;
  char *tmp = NULL;
  struct digestdata digest;
  char *ch = challenge;
  char cnoncebuf[33] = {0x0};

  ch += strlen("Digest ");

  digest.algorithm = NULL;
  digest.nonce = NULL;
  digest.cnonce = NULL;
  digest.opaque = NULL;
  digest.realm = NULL;
  digest.qop = NULL;

  if(auth_decode_digest_http_message(ch, &digest) != 0){
    printf("Digest decode error\r\n");
    return -1;
  }

  digest.nc = 1;
  memset(hashbuf,0x0,32);
  memset(cnoncebuf,0x0,33);

  lws_get_random(lws_get_context(wsi), cnoncebuf, sizeof(cnoncebuf));

  lws_b64_encode_string(cnoncebuf, (int)strlen(cnoncebuf), cnonce, 64);

  digest.cnonce = cnonce;

  if(digest.userhash)
  {
    hashthis = malloc(sizeof(char) * (strlen(user) + strlen(digest.realm) +2)  );
    sprintf(hashthis, "%s:%s", user, digest.realm ? digest.realm : "");
    if(!hashthis)
      return -1;

    md5_hash(hashbuf, (uint8_t *)hashthis, strlen(hashthis));
    free(hashthis);
    convert_to_ascii(hashbuf, (unsigned char*)userh);
  }

  /*
    If the algorithm is "MD5" or unspecified (which then defaults to MD5):

      A1 = unq(username-value) ":" unq(realm-value) ":" passwd

    If the algorithm is "MD5-sess" then:

      A1 = H(unq(username-value) ":" unq(realm-value) ":" passwd) ":"
           unq(nonce-value) ":" unq(cnonce-value)
  */

  hashthis = malloc(sizeof(char) * (strlen(user) + strlen(password) + strlen(digest.realm) +3)  );
  sprintf(hashthis,"%s:%s:%s", user, digest.realm ? digest.realm : "",
      password);
  if(!hashthis)
    return -1;



  md5_hash(hashbuf, (uint8_t *)hashthis, strlen(hashthis));
  free(hashthis);
  convert_to_ascii(hashbuf, ha1);
  tmp = malloc(sizeof(char) *(strlen((char *)ha1)+1+strlen(digest.nonce)+1+strlen(digest.cnonce)+1));
  if(digest.algo & SESSION_ALGO) {
    /* nonce and cnonce are OUTSIDE the hash */
    sprintf(tmp,"%s:%s:%s", ha1, digest.nonce, digest.cnonce);
    if(!tmp)
      return -1;

    md5_hash(hashbuf, (unsigned char *) tmp, strlen(tmp));
    free(tmp);
    convert_to_ascii(hashbuf, ha1);
  }

  /*
    If the "qop" directive's value is "auth" or is unspecified, then A2 is:

      A2 = Method ":" digest-uri-value

    If the "qop" value is "auth-int", then A2 is:

      A2 = Method ":" digest-uri-value ":" H(entity-body)

    (The "Method" value is the HTTP request method as specified in section
    5.1.1 of RFC 2616)
  */
  hashthis = malloc(sizeof(char) * (strlen(http_req) + strlen(uri) +2)  );
  sprintf(hashthis,"%s:%s", http_req, uri);
  if(!hashthis)
    return -1;

  if(digest.qop && strcasecmp(digest.qop, "auth-int") == 0) {
    /* We don't support auth-int for PUT or POST */
    char hashed[65];
    char *hashthis2;

    md5_hash(hashbuf, (uint8_t*)"", 0);
    convert_to_ascii(hashbuf, (unsigned char *)hashed);
    hashthis2 = malloc(sizeof(char) * (strlen(hashthis) + strlen(hashed) +2)  );
    sprintf(hashthis2, "%s:%s", hashthis, hashed);
    free(hashthis);
    hashthis = hashthis2;
  }

  if(!hashthis)
    return -1;

  md5_hash(hashbuf, (unsigned char *) hashthis, strlen(hashthis));
  free(hashthis);
  convert_to_ascii(hashbuf, ha2);

  if(digest.qop) {
    hashthis = malloc(sizeof(char) * (strlen((char *)ha1) + 1 +
                                      strlen(digest.nonce) + 1 +
                                      8 + 1 +
                                      strlen(digest.cnonce) + 1 +
                                      strlen(digest.qop) + 1) +
                                      strlen((char *)ha2) + 1);
    sprintf(hashthis,"%s:%s:%08x:%s:%s:%s", ha1, digest.nonce, digest.nc,
                       digest.cnonce, digest.qop, ha2);
  }
  else {
    hashthis = malloc(sizeof(char) * (strlen((char *)ha1) + 1 +
                                      strlen(digest.nonce) + 1 +
                                      strlen((char *)ha2) + 1));
    sprintf(hashthis,"%s:%s:%s", ha1, digest.nonce, ha2);
  }

  if(!hashthis)
    return -1;

  md5_hash(hashbuf, (unsigned char *) hashthis, strlen(hashthis));
  free(hashthis);
  convert_to_ascii(hashbuf, request_digest);

  /* For test case 64 (snooped from a Mozilla 1.3a request)

     Authorization: Digest username="testuser", realm="testrealm", \
     nonce="1053604145", uri="/64", response="c55f7f30d83d774a3d2dcacf725abaca"

     Digest parameters are all quoted strings.  Username which is provided by
     the user will need double quotes and backslashes within it escaped.
     realm, nonce, and opaque will need backslashes as well as they were
     de-escaped when copied from request header.  cnonce is generated with
     web-safe characters.  uri is already percent encoded.  nc is 8 hex
     characters.  algorithm and qop with standard values only contain web-safe
     characters.
  */
  userp_quoted = auth_digest_string_quoted(digest.userhash ? userh : user);
  if(!userp_quoted)
    return -1;
  if(digest.realm)
    realm_quoted = auth_digest_string_quoted(digest.realm);
  else {
    realm_quoted = malloc(1);
    if(realm_quoted)
      realm_quoted[0] = 0;
  }
  if(!realm_quoted) {
    free(userp_quoted);
    return -1;
  }
  nonce_quoted = auth_digest_string_quoted(digest.nonce);
  if(!nonce_quoted) {
    free(realm_quoted);
    free(userp_quoted);
    return -1;
  }

  if(digest.qop) {
    response = malloc(sizeof(char) * (strlen(userp_quoted) + 1 +
                                      strlen(realm_quoted) + 1 +
                                      strlen(nonce_quoted) + 1 +
                                      strlen(uri) + 1 +
                                      strlen(digest.cnonce) + 1 +
                                      8 + 1 +
                                      strlen(digest.qop) + 1 +
                                      strlen((char *)request_digest) + 1 +
                                      256));
    sprintf(response, "Digest username=\"%s\", "
                       "realm=\"%s\", "
                       "nonce=\"%s\", "
                       "uri=\"%s\", "
                       "cnonce=\"%s\", "
                       "nc=%08x, "
                       "qop=%s, "
                       "response=\"%s\"",
                       userp_quoted,
                       realm_quoted,
                       nonce_quoted,
                       uri,
                       digest.cnonce,
                       digest.nc,
                       digest.qop,
                       request_digest);

    /* Increment nonce-count to use another nc value for the next request */
    digest.nc++;
  }
  else {
    response = malloc(sizeof(char) * (strlen(userp_quoted) + 1 +
                                      strlen(realm_quoted) + 1 +
                                      strlen(nonce_quoted) + 1 +
                                      strlen(uri) + 1 +
                                      strlen((char *)request_digest) + 1 +
                                      128));
    sprintf(response,"Digest username=\"%s\", "
                       "realm=\"%s\", "
                       "nonce=\"%s\", "
                       "uri=\"%s\", "
                       "response=\"%s\"",
                       userp_quoted,
                       realm_quoted,
                       nonce_quoted,
                       uri,
                       request_digest);
  }
  free(nonce_quoted);
  free(realm_quoted);
  free(userp_quoted);
  if(!response)
    return -1;

  /* Add the optional fields */
  if(digest.opaque) {
    char *opaque_quoted;
    /* Append the opaque */
    opaque_quoted = auth_digest_string_quoted(digest.opaque);
    if(!opaque_quoted) {
      free(response);
      return -1;
    }
    tmp = malloc(sizeof(char)*strlen(response)+strlen(opaque_quoted)+16);
    sprintf(tmp,"%s, opaque=\"%s\"", response, opaque_quoted);
    free(response);
    free(opaque_quoted);
    if(!tmp)
      return -1;

    response = tmp;
  }

  if(digest.algorithm) {
    /* Append the algorithm */
    tmp = malloc(sizeof(char)*strlen(response)+strlen(digest.algorithm)+16);
    sprintf(tmp,"%s, algorithm=%s", response, digest.algorithm);
    free(response);
    if(!tmp)
      return -1;

    response = tmp;
  }

  if(digest.userhash) {
    /* Append the userhash */
    tmp = malloc(sizeof(char)*strlen(response)+16);
    sprintf(tmp,"%s, userhash=true", response);
    free(response);
    if(!tmp)
      return -1;

    response = tmp;
  }

  /* Return the output */
  *outptr = response;
  *outlen = strlen(response);

  return 0;

}
char *www_authenticate_buffer = NULL;
int auth_type = 0;
char path[512] ;
static int
callback_http(struct lws *wsi, enum lws_callback_reasons reason,
	      void *user, void *in, size_t len)
{

    printf("callback call reason %d status %d\r\n",reason,status );
    switch (reason) {

	/* because we are protocols[0] ... */
	case LWS_CALLBACK_CLIENT_CONNECTION_ERROR:
		lwsl_err("CLIENT_CONNECTION_ERROR: %s\n",
			 in ? (char *)in : "(null)");
		interrupted = 1;
		bad = 3; /* connection failed before we could make connection */
		lws_cancel_service(lws_get_context(wsi));

#if defined(LWS_WITH_CONMON)
	if (conmon)
		dump_conmon_data(wsi);
#endif
		break;

	case LWS_CALLBACK_ESTABLISHED_CLIENT_HTTP:
		{
			char buf[128];

			lws_get_peer_simple(wsi, buf, sizeof(buf));
			status = (int)lws_http_client_http_response(wsi);

#if defined(LWS_WITH_ALLOC_METADATA_LWS)
			_lws_alloc_metadata_dump_lws(lws_alloc_metadata_dump_stdout, NULL);
#endif

			lwsl_user("Connected to %s, http response: %d\n",
					buf, status);
		}
#if defined(LWS_WITH_HTTP2)
		if (long_poll) {
			lwsl_user("%s: Client entering long poll mode\n", __func__);
			lws_h2_client_stream_long_poll_rxonly(wsi);
		}
#endif

		if (lws_fi_user_wsi_fi(wsi, "user_reject_at_est"))
			return -1;

		if(lws_hdr_total_length(wsi, WSI_TOKEN_HTTP_WWW_AUTHENTICATE) > 0){
	        www_authenticate_buffer = malloc((size_t) lws_hdr_total_length(wsi, WSI_TOKEN_HTTP_WWW_AUTHENTICATE) +1);
	        memset(www_authenticate_buffer,0x0,(size_t)lws_hdr_total_length(wsi, WSI_TOKEN_HTTP_WWW_AUTHENTICATE) +1);
	        lws_hdr_copy(wsi,www_authenticate_buffer,1024,WSI_TOKEN_HTTP_WWW_AUTHENTICATE);
	        if(strncmp(www_authenticate_buffer,"Digest",5) == 0){
	          auth_type = 2;
	        }else if(strncmp(www_authenticate_buffer,"Basic",5) == 0){
	          auth_type = 1;
	        }
		}
#if 0
        int i = 0;
        for(i = 0;i<WSI_TOKEN_COUNT;i++){
          char buffer[1024];
          memset(buffer,0x0,1024);
          lws_hdr_copy(wsi,buffer,1024,i);
          printf("header %d %s\r\n",i,buffer);
        }
#endif
		break;
        /* you only need this if you need to do Basic Auth */
        case LWS_CALLBACK_CLIENT_APPEND_HANDSHAKE_HEADER:
	    {
	        unsigned char **p = (unsigned char **)in, *end = (*p) + len;

	        if (lws_add_http_header_by_token(wsi, WSI_TOKEN_HTTP_USER_AGENT,
	                (unsigned char *)ua, (int)strlen(ua), p, end))
	            return -1;

	        if (lws_add_http_header_by_token(wsi, WSI_TOKEN_HTTP_ACCEPT,
	                (unsigned char *)acc, (int)strlen(acc), p, end))
	            return -1;
#if defined(LWS_WITH_HTTP_BASIC_AUTH)
	        if(www_authenticate_buffer == NULL){


              char b[128];

              if (!ba_user || !ba_password)
                  break;

              if (lws_http_basic_auth_gen(ba_user, ba_password, b, sizeof(b)))
                  break;
              if (lws_add_http_header_by_token(wsi, WSI_TOKEN_HTTP_AUTHORIZATION,
                      (unsigned char *)b, (int)strlen(b), p, end))
                  return -1;
	        }else{
	          if(auth_type == 2){
	            printf("< WWW-Authenticate: %s\r\n",www_authenticate_buffer);
	            char *output = NULL;
	            size_t output_size = 0;

	            output_digest(wsi,"GET", path, (char *)ba_user, (char *)ba_password, www_authenticate_buffer, &output,&output_size);
	            printf("> Authorization: %s\r\n",output);
	            if (lws_add_http_header_by_token(wsi, WSI_TOKEN_HTTP_AUTHORIZATION,
	                      (unsigned char *)output, (int)output_size, p, end))
	                  return -1;
	            }
	          }

#endif
	        break;
	}

	/* chunks of chunked content, with header removed */
	case LWS_CALLBACK_RECEIVE_CLIENT_HTTP_READ:
		lwsl_user("RECEIVE_CLIENT_HTTP_READ: read %d\n", (int)len);
#if defined(LWS_WITH_HTTP2)
		if (long_poll) {
			char dotstar[128];
			lws_strnncpy(dotstar, (const char *)in, len,
				     sizeof(dotstar));
			lwsl_notice("long poll rx: %d '%s'\n", (int)len,
					dotstar);
		}
#endif
#if 0
		lwsl_hexdump_notice(in, len);
#endif

		return 0; /* don't passthru */

	/* uninterpreted http content */
	case LWS_CALLBACK_RECEIVE_CLIENT_HTTP:
		{
			char buffer[1024 + LWS_PRE];
			char *px = buffer + LWS_PRE;
			int lenx = sizeof(buffer) - LWS_PRE;

			if (lws_fi_user_wsi_fi(wsi, "user_reject_at_rx"))
				return -1;

			if (lws_http_client_read(wsi, &px, &lenx) < 0)
				return -1;
		}
		return 0; /* don't passthru */

	case LWS_CALLBACK_COMPLETED_CLIENT_HTTP:
		lwsl_user("LWS_CALLBACK_COMPLETED_CLIENT_HTTP\n");
		interrupted = 1;
		bad = status != 200;
		lws_cancel_service(lws_get_context(wsi)); /* abort poll wait */
		break;

	case LWS_CALLBACK_CLOSED_CLIENT_HTTP:
		interrupted = 1;
		bad = status != 200;
		lws_cancel_service(lws_get_context(wsi)); /* abort poll wait */
#if defined(LWS_WITH_CONMON)
		if (conmon)
			dump_conmon_data(wsi);
#endif
		break;

	default:
		break;
	}

    printf("lws_callback_http_dummy reason %d in %p len %lu\r\n",reason,in,len);
	return lws_callback_http_dummy(wsi, reason, user, in, len);
}

static const struct lws_protocols protocols[] = {
	{
		"http",
		callback_http,
		0, 0, 0, NULL, 0
	},
	LWS_PROTOCOL_LIST_TERM
};

static void
sigint_handler(int sig)
{
	interrupted = 1;
}

struct args {
	int argc;
	const char **argv;
};

static int
system_notify_cb(lws_state_manager_t *mgr, lws_state_notify_link_t *link,
		   int current, int target)
{
	struct lws_context *context = mgr->parent;
	struct lws_client_connect_info i;
	struct args *a = lws_context_user(context);
	const char *p;

	if (current != LWS_SYSTATE_OPERATIONAL || target != LWS_SYSTATE_OPERATIONAL)
		return 0;

	lwsl_info("%s: operational\n", __func__);

	memset(&i, 0, sizeof i); /* otherwise uninitialized garbage */
	i.context = context;
	if (!lws_cmdline_option(a->argc, a->argv, "-n")) {
		i.ssl_connection = LCCSCF_USE_SSL;
#if defined(LWS_WITH_HTTP2)
		/* requires h2 */
		if (lws_cmdline_option(a->argc, a->argv, "--long-poll")) {
			lwsl_user("%s: long poll mode\n", __func__);
			long_poll = 1;
		}
#endif
	}

	if (lws_cmdline_option(a->argc, a->argv, "-l")) {
		i.port = 7681;
		i.address = "localhost";
		i.ssl_connection |= LCCSCF_ALLOW_SELFSIGNED;
	} else {
		i.port = 443;
		i.address = "warmcat.com";
	}

	if (lws_cmdline_option(a->argc, a->argv, "--nossl"))
		i.ssl_connection = 0;

	i.ssl_connection |= LCCSCF_H2_QUIRK_OVERFLOWS_TXCR |
			    LCCSCF_ACCEPT_TLS_DOWNGRADE_REDIRECTS |
			    LCCSCF_H2_QUIRK_NGHTTP2_END_STREAM;

	i.alpn = "h2,http/1.1";
	if (lws_cmdline_option(a->argc, a->argv, "--h1"))
		i.alpn = "http/1.1";

	if (lws_cmdline_option(a->argc, a->argv, "--h2-prior-knowledge"))
		i.ssl_connection |= LCCSCF_H2_PRIOR_KNOWLEDGE;

	if ((p = lws_cmdline_option(a->argc, a->argv, "-p")))
		i.port = atoi(p);

	if ((p = lws_cmdline_option(a->argc, a->argv, "--user")))
		ba_user = p;
	if ((p = lws_cmdline_option(a->argc, a->argv, "--password")))
		ba_password = p;

	if (lws_cmdline_option(a->argc, a->argv, "-j"))
		i.ssl_connection |= LCCSCF_ALLOW_SELFSIGNED;

	if (lws_cmdline_option(a->argc, a->argv, "-k"))
		i.ssl_connection |= LCCSCF_ALLOW_INSECURE;

	if (lws_cmdline_option(a->argc, a->argv, "-b"))
		i.ssl_connection |= LCCSCF_CACHE_COOKIES;

	if (lws_cmdline_option(a->argc, a->argv, "-m"))
		i.ssl_connection |= LCCSCF_SKIP_SERVER_CERT_HOSTNAME_CHECK;

	if (lws_cmdline_option(a->argc, a->argv, "-e"))
		i.ssl_connection |= LCCSCF_ALLOW_EXPIRED;

	if ((p = lws_cmdline_option(a->argc, a->argv, "-f"))) {
		i.ssl_connection |= LCCSCF_H2_MANUAL_RXFLOW;
		i.manual_initial_tx_credit = atoi(p);
		lwsl_notice("%s: manual peer tx credit %d\n", __func__,
				i.manual_initial_tx_credit);
	}

#if defined(LWS_WITH_CONMON)
	if (lws_cmdline_option(a->argc, a->argv, "--conmon")) {
		i.ssl_connection |= LCCSCF_CONMON;
		conmon = 1;
	}
#endif

	/* the default validity check is 5m / 5m10s... -v = 3s / 10s */

	if (lws_cmdline_option(a->argc, a->argv, "-v"))
		i.retry_and_idle_policy = &retry;

	if ((p = lws_cmdline_option(a->argc, a->argv, "--server")))
		i.address = p;

	if ((p = lws_cmdline_option(a->argc, a->argv, "--path")))
		i.path = p;
	else
		i.path = "/";
	memset(path,0x0,512);
	strncpy(path,i.path,512);
	i.host = i.address;
	i.origin = i.address;
	i.method = "GET";

	i.protocol = protocols[0].name;
	i.pwsi = &client_wsi;
	i.fi_wsi_name = "user";

	if (!lws_client_connect_via_info(&i)) {
		lwsl_err("Client creation failed\n");
		interrupted = 1;
		bad = 2; /* could not even start client connection */
		lws_cancel_service(context);

		return 1;
	}

	if (close_after_start)
		lws_wsi_close(client_wsi, LWS_TO_KILL_SYNC);

	return 0;
}

int main(int argc, const char **argv)
{
	lws_state_notify_link_t notifier = { { NULL, NULL, NULL },
					     system_notify_cb, "app" };
	lws_state_notify_link_t *na[] = { &notifier, NULL };
	struct lws_context_creation_info info;
	struct lws_context *context;
	int n = 0, expected = 0;
	struct args args;
	const char *p;
	// uint8_t memcert[4096];

	args.argc = argc;
	args.argv = argv;

	signal(SIGINT, sigint_handler);

	memset(&info, 0, sizeof info); /* otherwise uninitialized garbage */
	lws_cmdline_option_handle_builtin(argc, argv, &info);

	lwsl_user("LWS minimal http client [-d<verbosity>] [-l] [--h1]\n");

	info.options = LWS_SERVER_OPTION_DO_SSL_GLOBAL_INIT |
		       LWS_SERVER_OPTION_H2_JUST_FIX_WINDOW_UPDATE_OVERFLOW;
	info.port = CONTEXT_PORT_NO_LISTEN; /* we do not run any server */
	info.protocols = protocols;
	info.user = &args;
	info.register_notifier_list = na;
	info.connect_timeout_secs = 30;

#if defined(LWS_WITH_CACHE_NSCOOKIEJAR)
	info.http_nsc_filepath = "./cookies.txt";
	if ((p = lws_cmdline_option(argc, argv, "-c")))
		info.http_nsc_filepath = p;
#endif

	/*
	 * since we know this lws context is only ever going to be used with
	 * one client wsis / fds / sockets at a time, let lws know it doesn't
	 * have to use the default allocations for fd tables up to ulimit -n.
	 * It will just allocate for 1 internal and 1 (+ 1 http2 nwsi) that we
	 * will use.
	 */
	info.fd_limit_per_thread = 1 + 1 + 1;

	if (lws_cmdline_option(argc, argv, "--cos"))
		close_after_start = 1;

#if defined(LWS_WITH_MBEDTLS) || defined(USE_WOLFSSL)
	/*
	 * OpenSSL uses the system trust store.  mbedTLS has to be told which
	 * CA to trust explicitly.
	 */
	if (lws_cmdline_option(argc, argv, "-w"))
		/* option to confirm we are validating against the right cert */
		info.client_ssl_ca_filepath = "./wrong.cer";
	else
		info.client_ssl_ca_filepath = "./warmcat.com.cer";
#endif
#if 0
	n = open("./warmcat.com.cer", O_RDONLY);
	if (n >= 0) {
		info.client_ssl_ca_mem_len = read(n, memcert, sizeof(memcert));
		info.client_ssl_ca_mem = memcert;
		close(n);
		n = 0;
		memcert[info.client_ssl_ca_mem_len++] = '\0';
	}
#endif
	context = lws_create_context(&info);
	if (!context) {
		lwsl_err("lws init failed\n");
		bad = 5;
		goto bail;
	}

	while (n >= 0 && !interrupted)
		n = lws_service(context, 0);

	lws_context_destroy(context);

bail:
	if ((p = lws_cmdline_option(argc, argv, "--expected-exit")))
		expected = atoi(p);

	if (bad == expected) {
		lwsl_user("Completed: OK (seen expected %d)\n", expected);
		return 0;
	} else
		lwsl_err("Completed: failed: exit %d, expected %d\n", bad, expected);

	return 1;
}
