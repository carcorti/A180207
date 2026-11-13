/* A180207: ordered length-four window permutations.
 * Copyright (c) 2026 Carlo Corti.
 * C17 + unsigned __int128, POSIX/Linux, OpenMP and OpenSSL EVP.
 * Mathematical specification and operational limits: review dossier.
 * One-sided zero-boundary weighted subset DP, then complement products.
 * No quotient by symmetry. No scientific external executable is used.
 * Wire records are little-endian key/low/high (24 bytes), never native structs.
 */
#define _POSIX_C_SOURCE 200809L
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <omp.h>
#include <openssl/evp.h>
#include <openssl/crypto.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <time.h>
#include <unistd.h>
#ifndef SOURCE_SHA
#define SOURCE_SHA "UNBOUND"
#endif
#ifndef MAKE_SHA
#define MAKE_SHA "UNBOUND"
#endif
#if !defined(__SIZEOF_INT128__) || __SIZEOF_INT128__ != 16
#error unsigned 128-bit arithmetic required
#endif
__extension__ typedef unsigned __int128 U128;
typedef struct { uint64_t key, lo, hi; } Rec;
_Static_assert(sizeof(Rec)==24, "allocation model requires 24-byte records");
_Static_assert(sizeof(size_t)==8 && sizeof(off_t)==8, "64-bit size/off required");
_Static_assert(sizeof(double)==8 && FLT_RADIX==2 && DBL_MANT_DIG==53 && DBL_MAX_EXP==1024, "IEEE binary64 receipt format required");
#define MAX_M 24U
#define MAX_W 8U
#define RAM_LIMIT (UINT64_C(44)<<30)
#define DISK_LIMIT (UINT64_C(64)<<30)
#define FIXED (UINT64_C(64)<<20)
#define EMPTY UINT64_MAX
#define CHUNK UINT64_C(8192)
#define SCHEMA UINT64_C(2)
static const char *const names[]={"run.json","chk0.bin","chk1.bin","chk.tmp","res.tsv","log.txt","sha.txt","lock"};
static volatile sig_atomic_t stopping=0;
static _Atomic uint64_t allocated=0, highwater=0;
static U128 factorial[25];
static uint32_t suffix[25];
static char binary_hex[65];
static double now(void) { struct timespec t; if(clock_gettime(CLOCK_MONOTONIC,&t)) return 0; return (double)t.tv_sec+(double)t.tv_nsec*1e-9; }
static void onsignal(int s) { (void)s; stopping=1; }
static void message(const char *s) { fprintf(stderr,"a180207: %s\n",s); }
static bool add128(U128 a,U128 b,U128 *out) { *out=a+b; return *out>=a; }
static bool mul128(U128 a,U128 b,U128 *out) { if(b && a>(~(U128)0)/b) return false; *out=a*b; return true; }
static bool count64(uint64_t *v,uint64_t x) { if(*v>UINT64_MAX-x) return false; *v+=x; return true; }
static U128 value(Rec r) { return ((U128)r.hi<<64)|r.lo; }
static Rec record(uint64_t k,U128 v) { Rec r={k,(uint64_t)v,(uint64_t)(v>>64)}; return r; }
static void decimal(U128 x,char buf[40]) { char tmp[40]; unsigned n=0; do { tmp[n++]=(char)('0'+x%10); x/=10; } while(x); for(unsigned i=0;i<n;i++) buf[i]=tmp[n-1-i]; buf[n]=0; }
static uint64_t choose(unsigned n,unsigned k) { uint64_t x=1; if(k>n) return 0; if(k>n-k) k=n-k; for(unsigned i=1;i<=k;i++) x=x*(n-k+i)/i; return x; }
static void init_math(unsigned N) { factorial[0]=1; for(unsigned i=1;i<=24;i++) factorial[i]=factorial[i-1]*i; uint32_t full=(UINT32_C(1)<<N)-1U; for(unsigned i=0;i<=24;i++) suffix[i]=(i<=1)?full:((i<=N)?(full&~((UINT32_C(1)<<(i-1))-1U)):0); }
static void *getmem(uint64_t bytes) {
    if(!bytes) return NULL;
    uint64_t old=atomic_load(&allocated);
    do { if(bytes>RAM_LIMIT || old>RAM_LIMIT-bytes) return NULL; } while(!atomic_compare_exchange_weak(&allocated,&old,old+bytes));
    void *p=NULL;
    if(posix_memalign(&p,64,(size_t)bytes)) { atomic_fetch_sub(&allocated,bytes); return NULL; }
    uint64_t peak=atomic_load(&highwater);
    while(peak<old+bytes && !atomic_compare_exchange_weak(&highwater,&peak,old+bytes)) {}
    return p;
}
static void putmem(void *p,uint64_t bytes) { if(p) { free(p); atomic_fetch_sub(&allocated,bytes); } }
static uint64_t hkey(uint64_t x) { x^=x>>30; x*=UINT64_C(0xbf58476d1ce4e5b9); x^=x>>27; x*=UINT64_C(0x94d049bb133111eb); return x^(x>>31); }
typedef struct { Rec *slot; uint64_t cap, used; } Table;
static uint64_t tablecap(uint64_t n) { uint64_t c=16; while((c/10)*7+(c%10)*7/10<n) { if(c>UINT64_MAX/2) return 0; c*=2; } return c; }
static bool table_init(Table *t,uint64_t cap) { if(cap<16 || (cap&(cap-1)) || cap>RAM_LIMIT/24) return false; t->slot=getmem(cap*24); if(!t->slot) return false; t->cap=cap;t->used=0;for(uint64_t i=0;i<cap;i++) t->slot[i].key=EMPTY;return true; }
static void table_free(Table *t) { putmem(t->slot,24*t->cap); memset(t,0,sizeof(*t)); }
static bool raw_insert(Table *t,Rec r,bool unique) {
    uint64_t i=hkey(r.key)&(t->cap-1);
    while(t->slot[i].key!=EMPTY && t->slot[i].key!=r.key) i=(i+1)&(t->cap-1);
    if(t->slot[i].key==EMPTY) { t->slot[i]=r;t->used++;return true; }
    U128 x;
    if(unique || !add128(value(t->slot[i]),value(r),&x)) return false;
    t->slot[i]=record(r.key,x); return true;
}
static bool insert(Table *t,Rec r) {
    if(!t->cap && !table_init(t,16)) return false;
    if(t->used+1>(t->cap/10)*7+(t->cap%10)*7/10) {
        Table fresh={0}; if(!table_init(&fresh,t->cap*2)) return false;
        for(uint64_t i=0;i<t->cap;i++) if(t->slot[i].key!=EMPTY && !raw_insert(&fresh,t->slot[i],true)) { table_free(&fresh); return false; }
        table_free(t); *t=fresh;
    }
    return raw_insert(t,r,false);
}
/* Stable 3 x 16-bit radix sort. Current is freed before vector extraction;
 * table is freed before scratch. Scratch plus vector is exactly 48*len.
 */
static bool radix(Rec *v,uint64_t len) {
    if(len<2) return true;
    Rec *tmp=getmem(24*len); uint64_t *bins=getmem(UINT64_C(65536)*8);
    if(!tmp || !bins) {putmem(tmp,24*len);putmem(bins,UINT64_C(65536)*8);return false;}
    Rec *a=v,*b=tmp;
    for(unsigned p=0;p<3;p++) {
        memset(bins,0,65536*8);
        for(uint64_t i=0;i<len;i++) bins[(a[i].key>>(16*p))&65535]++;
        uint64_t sum=0;
        for(unsigned j=0;j<65536;j++) {uint64_t z=bins[j];bins[j]=sum;sum+=z;}
        for(uint64_t i=0;i<len;i++) b[bins[(a[i].key>>(16*p))&65535]++]=a[i];
        Rec *s=a;a=b;b=s;
    }
    memcpy(v,a,(size_t)(24*len));putmem(tmp,24*len);putmem(bins,UINT64_C(65536)*8);return true;
}
typedef struct {
    _Alignas(64) U128 *F;
    Rec *cur; Table next;
    uint64_t len,pos,prefix,states,transitions;
    unsigned layer,active;
    int error;
} Worker;
_Static_assert(sizeof(Worker)%64==0 && _Alignof(Worker)>=64,"worker isolation");
typedef struct {
    unsigned M,N,m,d,phase,reduce_worker,out_n;
    uint64_t masks,atoms,generation,invocations,redpos,convpos;
    U128 convsum,result[25];
    Worker w[MAX_W];
    uint64_t mem_bound,snap_bound,start_states,start_transitions;
    unsigned actual_workers;
    double invocation_limit,invocation_service,cut_elapsed;
} Job;
/* No fitted state counts enter this upper bound. B bounds all triples.
 * Each fixed increasing d-prefix leaves at most choose(N-d,k)*B keys.
 */
static bool bounds(unsigned M,unsigned m,unsigned d,uint64_t *mem,uint64_t *snap) {
    if(M<1 || M>MAX_M || m<1 || m>8 || d>4 || d>M-1 || (d==0 && m!=1)) return false;
    unsigned N=M-1,R=N-d; uint64_t B=choose(N+3,3),f=(UINT64_C(1)<<N)*16,peak=0,payload=0;
    for(unsigned k=0;k<=R;k++) {
        uint64_t a=B*choose(R,k),b=(k<R)?B*choose(R,k+1):0,c=tablecap(b);
        uint64_t v=24*a+36*c;
        if(v>peak) peak=v;
        v=24*(b+c);if(v>peak) peak=v;
        v=48*b;if(v>peak) peak=v;
        v=24*(a+b);if(v>payload) payload=v;
    }
    *mem=m*(peak+f+FIXED); *snap=m*(payload+f+4096)+4096;
    return *mem<=RAM_LIMIT && *snap<=(DISK_LIMIT-FIXED)/3;
}
static bool prefix_start(Job *j,Worker *w) {
    unsigned v[4]={0},last=0; uint64_t rank=w->prefix; uint32_t mask=0;unsigned a=0,b=0,c=0;
    for(unsigned i=0;i<j->d;i++) {
        unsigned x=last+1;
        for(;x<=j->N;x++) {uint64_t block=choose(j->N-x,j->d-i-1);if(rank<block) break;rank-=block;}
        if(x>j->N) return false;
        v[i]=x; mask|=UINT32_C(1)<<(x-1);unsigned z=x-last;a=b;b=c;c=z;last=x;
    }
    (void)v;
    w->cur=getmem(24);if(!w->cur) return false;
    w->cur[0]=record(((uint64_t)mask<<15)|((uint64_t)a<<10)|((uint64_t)b<<5)|c,1);
    w->len=1;w->pos=0;w->layer=j->d;w->active=1;return true;
}
static bool next_layer(Worker *w) {
    putmem(w->cur,24*w->len);w->cur=NULL;w->len=0;w->pos=0;
    uint64_t n=w->next.used;
    if(!n) {table_free(&w->next);w->active=0;return true;}
    Rec *v=getmem(24*n);if(!v) return false;
    uint64_t at=0;for(uint64_t i=0;i<w->next.cap;i++) if(w->next.slot[i].key!=EMPTY) v[at++]=w->next.slot[i];
    table_free(&w->next);
    if(at!=n || !radix(v,n)) {putmem(v,24*n);return false;}
    w->cur=v;w->len=n;w->layer++;return true;
}
static bool work(Job *j,Worker *w,uint64_t quota) {
    uint32_t full=(uint32_t)(j->masks-1);
    if(!w->active) { if(w->prefix>=j->atoms) return true; if(!prefix_start(j,w)) return false; }
    uint64_t done=0;
    while(w->pos<w->len && done<quota) {
        Rec r=w->cur[w->pos];uint32_t used=(uint32_t)(r.key>>15);
        unsigned a=(unsigned)((r.key>>10)&31),b=(unsigned)((r.key>>5)&31),c=(unsigned)(r.key&31),sum=a+b+c;
        U128 weight=value(r),f;
        if(sum>j->N || !add128(w->F[used],weight,&f) || f>factorial[w->layer]) return false;
        w->F[used]=f;
        uint32_t choices=(full^used)&suffix[sum];
        while(choices) {
            unsigned bit=(unsigned)__builtin_ctz(choices),v=bit+1;choices&=choices-1;
            uint32_t mask=used|(UINT32_C(1)<<bit);
            uint64_t key=((uint64_t)mask<<15)|((uint64_t)b<<10)|((uint64_t)c<<5)|(v-sum);
            if(!insert(&w->next,record(key,weight)) || !count64(&w->transitions,1)) return false;
        }
        if(!count64(&w->states,1)) return false;
        w->pos++;done++;
    }
    if(w->pos==w->len) {
        if(!next_layer(w)) return false;
        if(!w->active) { if(!count64(&w->prefix,j->m)) return false; }
    }
    return true;
}
static bool new_job(Job *j) {
    for(unsigned t=0;t<j->m;t++) {
        j->w[t].F=getmem(16*j->masks);if(!j->w[t].F) return false;
        memset(j->w[t].F,0,(size_t)(16*j->masks));j->w[t].prefix=t;
    }
    for(uint64_t s=0;s<j->masks;s++) if((unsigned)__builtin_popcountll(s)<j->d) j->w[0].F[s]=1;
    j->phase=0;j->reduce_worker=1;j->out_n=1;return true;
}
static bool advance(Job *j) {
    if(j->phase==0) {
        #pragma omp parallel num_threads(j->m) default(none) shared(j)
        {
            #pragma omp single
            j->actual_workers=(unsigned)omp_get_num_threads();
            #pragma omp for schedule(static,1)
            for(unsigned t=0;t<j->m;t++) if(!work(j,&j->w[t],CHUNK)) j->w[t].error=1;
        }
        bool finished=true;
        for(unsigned t=0;t<j->m;t++) {if(j->w[t].error) return false;if(j->w[t].active || j->w[t].prefix<j->atoms) finished=false;}
        if(finished) j->phase=1;
    } else if(j->phase==1) {
        if(j->reduce_worker>=j->m) {j->phase=2;j->redpos=0;return true;}
        uint64_t end=j->redpos+CHUNK;if(end>j->masks) end=j->masks;
        for(;j->redpos<end;j->redpos++) {
            U128 z;uint64_t s=j->redpos;
            if(!add128(j->w[0].F[s],j->w[j->reduce_worker].F[s],&z) || z>factorial[__builtin_popcountll(s)]) return false;
            j->w[0].F[s]=z;
        }
        if(j->redpos==j->masks) {j->redpos=0;j->reduce_worker++;}
    } else if(j->phase==2) {
        unsigned n=j->out_n;
        if(n==1) {j->result[1]=1;j->out_n=2;}
        else {
            uint64_t half=UINT64_C(1)<<(n-2),full=2*half-1,end=j->convpos+CHUNK;if(end>half) end=half;
            for(;j->convpos<end;j->convpos++) {
                U128 p,z;if(!mul128(j->w[0].F[j->convpos],j->w[0].F[full^j->convpos],&p) || !add128(j->convsum,p,&z)) return false;
                j->convsum=z;
            }
            if(j->convpos==half) {
                if(!mul128(j->convsum,2,&j->result[n]) || j->result[n]>factorial[n]) return false;
                j->out_n++;j->convpos=0;j->convsum=0;
            }
        }
        if(j->out_n>j->M) j->phase=3;
    }
    return true;
}
static void cleanup(Job *j) {for(unsigned t=0;t<MAX_W;t++) {Worker *w=&j->w[t];putmem(w->F,16*j->masks);putmem(w->cur,24*w->len);table_free(&w->next);memset(w,0,sizeof(*w));}}
static void hex(const unsigned char raw[32],char out[65]) {static const char digits[]="0123456789abcdef";for(unsigned i=0;i<32;i++) {out[2*i]=digits[raw[i]>>4];out[2*i+1]=digits[raw[i]&15];}out[64]=0;}
static bool hashfd(int fd,uint64_t bytes,unsigned char out[32]) {
    EVP_MD_CTX *ctx=EVP_MD_CTX_new();bool ok=ctx && EVP_DigestInit_ex(ctx,EVP_sha256(),NULL)==1;unsigned char buf[65536];
    while(ok && bytes) {size_t want=bytes<sizeof(buf)?(size_t)bytes:sizeof(buf);ssize_t n=read(fd,buf,want);if(n<0 && errno==EINTR) continue;if(n<=0) {ok=false;break;}ok=EVP_DigestUpdate(ctx,buf,(size_t)n)==1;bytes-=(uint64_t)n;}
    unsigned len=0;if(ok) ok=EVP_DigestFinal_ex(ctx,out,&len)==1 && len==32;EVP_MD_CTX_free(ctx);return ok;
}
static int regular(int dir,const char *name,int flags) {
    int fd=openat(dir,name,flags|O_CLOEXEC|O_NOFOLLOW,0600);struct stat st;
    if(fd<0) return -1;
    if(fstat(fd,&st) || !S_ISREG(st.st_mode) || st.st_nlink!=1) {close(fd);return -1;}return fd;
}
/* Persist the namespace link as well as the contents of a fresh job root.
 * Reject empty/trailing-slash/dot final components; the parent must be a
 * real directory, and openat never follows a symlink at the job component.
 */
static int open_root(const char *root,bool checking,bool *fresh) {
    size_t n=strlen(root);char path[PATH_MAX];
    if(!n || n>=sizeof(path) || root[n-1]=='/') {errno=EINVAL;return -1;}
    memcpy(path,root,n+1);char *base=strrchr(path,'/');const char *parent=".";
    if(base) { *base=0;base++;parent=*path?path:"/"; } else base=path;
    if(!*base || strlen(base)>NAME_MAX || !strcmp(base,".") || !strcmp(base,"..")) {errno=EINVAL;return -1;}
    int pd=open(parent,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);if(pd<0) return -1;
    *fresh=false;
    if(!checking) {
        if(!mkdirat(pd,base,0700)) *fresh=true;
        else if(errno!=EEXIST) {int e=errno;close(pd);errno=e;return -1;}
    }
    int dir=openat(pd,base,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    int error=errno;
    if(dir>=0 && *fresh && fsync(pd)) {error=errno;close(dir);dir=-1;}
    close(pd);errno=error;return dir;
}
static bool writeall(int fd,const void *p,size_t n) {const unsigned char *b=p;while(n) {ssize_t z=write(fd,b,n);if(z<0 && errno==EINTR) continue;if(z<=0) return false;b+=(size_t)z;n-=(size_t)z;}return true;}
static bool readall(int fd,void *p,size_t n) {unsigned char *b=p;while(n) {ssize_t z=read(fd,b,n);if(z<0 && errno==EINTR) continue;if(z<=0) return false;b+=(size_t)z;n-=(size_t)z;}return true;}
static bool textfile(int dir,const char *name,const char *text,bool exclusive) {
    int fd=regular(dir,name,O_WRONLY|O_CREAT|(exclusive?O_EXCL:O_TRUNC));if(fd<0) return false;
    bool ok=writeall(fd,text,strlen(text));if(fsync(fd)) ok=false;if(close(fd)) ok=false;if(fsync(dir)) ok=false;return ok;
}
static bool inventory(int dir,uint64_t *size) {
    int dupfd=openat(dir,".",O_RDONLY|O_DIRECTORY|O_CLOEXEC);if(dupfd<0) return false;DIR *d=fdopendir(dupfd);if(!d) {close(dupfd);return false;}struct dirent *e;bool ok=true;*size=0;
    errno=0;
    while((e=readdir(d))) {
        if(!strcmp(e->d_name,".") || !strcmp(e->d_name,"..")) continue;
        bool known=false;for(unsigned i=0;i<8;i++) if(!strcmp(names[i],e->d_name)) known=true;
        struct stat st;if(!known || fstatat(dir,e->d_name,&st,AT_SYMLINK_NOFOLLOW) || !S_ISREG(st.st_mode) || st.st_nlink!=1 || st.st_size<0) {ok=false;break;}
        if(!count64(size,(uint64_t)st.st_size) || *size>DISK_LIMIT) {ok=false;break;}
    }
    if(errno) ok=false;
    if(closedir(d)) ok=false;
    return ok;
}
/* Digest is over every preceding byte. Integers are explicitly LE64.
 * Buffered streaming keeps checkpoint RAM constant; no state-sized copy.
 */
typedef struct {int fd;EVP_MD_CTX *md;unsigned char buffer[65536];size_t used;bool ok;uint64_t bytes;} Wire;
static void wire_init(Wire *s,int fd) {memset(s,0,sizeof(*s));s->fd=fd;s->md=EVP_MD_CTX_new();s->ok=s->md && EVP_DigestInit_ex(s->md,EVP_sha256(),NULL)==1;}
static void flush(Wire *s) {if(s->ok && s->used) s->ok=writeall(s->fd,s->buffer,s->used) && EVP_DigestUpdate(s->md,s->buffer,s->used)==1;s->used=0;}
static void bytes_out(Wire *s,const void *p,size_t n) {const unsigned char *b=p;while(s->ok && n) {size_t k=sizeof(s->buffer)-s->used;if(k>n) k=n;memcpy(s->buffer+s->used,b,k);s->used+=k;b+=k;n-=k;s->bytes+=k;if(s->used==sizeof(s->buffer)) flush(s);}}
static void u64out(Wire *s,uint64_t x) {unsigned char b[8];for(unsigned i=0;i<8;i++) b[i]=(unsigned char)(x>>(8*i));bytes_out(s,b,8);}
static void u128out(Wire *s,U128 x) {u64out(s,(uint64_t)x);u64out(s,(uint64_t)(x>>64));}
static void doubleout(Wire *s,double x) {uint64_t bits;memcpy(&bits,&x,8);u64out(s,bits);}
static void recout(Wire *s,Rec r) {u64out(s,r.key);u64out(s,r.lo);u64out(s,r.hi);}
typedef struct {int fd;unsigned char buf[65536];size_t pos,len;uint64_t consumed;bool ok;} Reader;
static void input(Reader *r,void *dst,size_t n) {
    unsigned char *p=dst;
    while(r->ok && n) {
        if(r->pos==r->len) {
            ssize_t z;do {z=read(r->fd,r->buf,sizeof(r->buf));} while(z<0 && errno==EINTR);
            if(z<=0) {r->ok=false;break;}r->pos=0;r->len=(size_t)z;
        }
        size_t k=r->len-r->pos;if(k>n) k=n;memcpy(p,r->buf+r->pos,k);r->pos+=k;r->consumed+=k;p+=k;n-=k;
    }
}
static uint64_t u64in(Reader *r) {unsigned char b[8]={0};uint64_t x=0;input(r,b,8);for(unsigned i=0;i<8;i++) x|=(uint64_t)b[i]<<(8*i);return x;}
static U128 u128in(Reader *r) {uint64_t lo=u64in(r),hi=u64in(r);return ((U128)hi<<64)|lo;}
static double doublein(Reader *r) {uint64_t bits=u64in(r);double x;memcpy(&x,&bits,8);return x;}
static Rec recin(Reader *r) {Rec x;x.key=u64in(r);x.lo=u64in(r);x.hi=u64in(r);return x;}
static void identities(char b[195]) {snprintf(b,195,"%s\n%s\n%s",SOURCE_SHA,MAKE_SHA,binary_hex);}
static bool save(Job *j,int dir) {
    if(j->generation>=UINT64_MAX-1) {message("checkpoint generation exhausted; no temporary or overwrite");return false;}
    uint64_t live;if(!inventory(dir,&live) || live>DISK_LIMIT-j->snap_bound) return false;
    struct statvfs v;if(fstatvfs(dir,&v) || v.f_frsize==0 || v.f_bavail<j->snap_bound/v.f_frsize+1) return false;
    /* Three full generations plus fixed text allowance were admitted up front. */
    int fd=regular(dir,"chk.tmp",O_WRONLY|O_CREAT|O_EXCL);if(fd<0) return false;
    Wire s;wire_init(&s,fd);bytes_out(&s,"A180207\0",8);u64out(&s,SCHEMA);char id[195];identities(id);bytes_out(&s,id,194);
    u64out(&s,j->M);u64out(&s,j->m);u64out(&s,j->d);u64out(&s,j->generation+1);u64out(&s,j->invocations);
    u64out(&s,j->phase);u64out(&s,j->reduce_worker);u64out(&s,j->redpos);u64out(&s,j->out_n);u64out(&s,j->convpos);u128out(&s,j->convsum);
    for(unsigned n=1;n<=24;n++) u128out(&s,j->result[n]);
    doubleout(&s,j->invocation_limit);doubleout(&s,j->invocation_service);doubleout(&s,j->cut_elapsed);
    for(unsigned t=0;t<j->m;t++) {
        Worker *w=&j->w[t];u64out(&s,w->prefix);u64out(&s,w->states);u64out(&s,w->transitions);u64out(&s,w->layer);u64out(&s,w->active);u64out(&s,w->len);u64out(&s,w->pos);u64out(&s,w->next.cap);u64out(&s,w->next.used);
        for(uint64_t i=0;i<j->masks;i++) u128out(&s,w->F[i]);
        for(uint64_t i=0;i<w->len;i++) recout(&s,w->cur[i]);
        for(uint64_t i=0;i<w->next.cap;i++) if(w->next.slot[i].key!=EMPTY) recout(&s,w->next.slot[i]);
    }
    flush(&s);unsigned char digest[32];unsigned n=0;
    if(s.ok) s.ok=EVP_DigestFinal_ex(s.md,digest,&n)==1 && n==32 && writeall(fd,digest,32);
    EVP_MD_CTX_free(s.md);if(s.bytes+32>j->snap_bound) s.ok=false;
    if(fsync(fd)) s.ok=false;
    if(close(fd)) s.ok=false;
    if(!s.ok) {message("checkpoint write failed; committed generations preserved; inspect chk.tmp");return false;}
    char dest[16];snprintf(dest,sizeof(dest),"chk%u.bin",(unsigned)((j->generation+1)&1));
    if(renameat(dir,"chk.tmp",dir,dest) || fsync(dir)) return false;
    j->generation++;
    fprintf(stderr,"checkpoint generation=%"PRIu64" bytes=%"PRIu64" committed_phase=%u\n",j->generation,s.bytes+32,j->phase);return true;
}
/* -1 missing, 0 corrupt, 1 valid, 2 foreign. Hash before trusting any length. */
static int inspect(int dir,const char *name,const Job *j,uint64_t *generation) {
    int fd=regular(dir,name,O_RDONLY);if(fd<0) return errno==ENOENT?-1:0;
    struct stat st;unsigned char digest[32],expected[32];bool ok=fstat(fd,&st)==0 && st.st_size>=800 && (uint64_t)st.st_size<=j->snap_bound;
    if(ok) ok=hashfd(fd,(uint64_t)st.st_size-32,digest) && readall(fd,expected,32) && !memcmp(digest,expected,32);
    if(!ok) {close(fd);return 0;}
    if(lseek(fd,0,SEEK_SET)<0) {close(fd);return 0;}
    Reader r={.fd=fd,.ok=true};char magic[8]={0},id[195]={0},want[195];input(&r,magic,8);
    uint64_t schema=u64in(&r);input(&r,id,194);identities(want);
    uint64_t M=u64in(&r),m=u64in(&r),d=u64in(&r);*generation=u64in(&r);
    close(fd);
    if(!r.ok || memcmp(magic,"A180207\0",8)) return 0;
    if(!*generation || *generation==UINT64_MAX) return 2;
    if(schema!=SCHEMA || memcmp(id,want,194) || M!=j->M || m!=j->m || d!=j->d) return 2;
    return 1;
}

static bool valid_rec(Job *j,Rec r,unsigned layer) {
    uint64_t mask=r.key>>15;unsigned a=(unsigned)((r.key>>10)&31),b=(unsigned)((r.key>>5)&31),c=(unsigned)(r.key&31);
    return r.key< (UINT64_C(1)<<38) && mask<j->masks && (unsigned)__builtin_popcountll(mask)==layer && a+b+c<=j->N && value(r)>0 && value(r)<=factorial[layer];
}
static bool load(Job *j,int dir,const char *name) {
    int fd=regular(dir,name,O_RDONLY);if(fd<0) return false;bool ok=true;char head[218];
    Reader reader={.fd=fd,.ok=true};input(&reader,head,218);ok=reader.ok; /* 8 magic + 8 schema + 194 identity + 8 M */
    uint64_t m=u64in(&reader),d=u64in(&reader);
    if(m!=j->m || d!=j->d) ok=false;
    j->generation=u64in(&reader);j->invocations=u64in(&reader);
    if(!j->generation || j->generation==UINT64_MAX) ok=false;
    uint64_t phase=u64in(&reader),rw=u64in(&reader);j->redpos=u64in(&reader);uint64_t on=u64in(&reader);j->convpos=u64in(&reader);j->convsum=u128in(&reader);
    if(phase>3 || rw<1 || rw>j->m || on<1 || on>j->M+1 || j->redpos>=j->masks || j->convpos>=j->masks || j->convsum>factorial[j->M]) ok=false;
    j->phase=(unsigned)phase;j->reduce_worker=(unsigned)rw;j->out_n=(unsigned)on;
    for(unsigned n=1;n<=24;n++) {j->result[n]=u128in(&reader);if(j->result[n]>factorial[n]) ok=false;}
    j->invocation_limit=doublein(&reader);j->invocation_service=doublein(&reader);j->cut_elapsed=doublein(&reader);
    if(!reader.ok || !isfinite(j->invocation_limit) || !isfinite(j->invocation_service) || !isfinite(j->cut_elapsed) || j->invocation_service<0 || j->cut_elapsed<0 || j->invocation_service>j->cut_elapsed+0.000001 ||
       (j->invocations?(j->invocation_limit<=0 || j->invocation_limit>3000):(j->invocation_limit!=0 || j->invocation_service!=0 || j->cut_elapsed!=0))) ok=false;
    uint64_t work_bound=choose(j->N+3,3)*j->atoms*(UINT64_C(1)<<(j->N-j->d));
    unsigned R=j->N-j->d;uint64_t transition_bound=R?choose(j->N+3,3)*j->atoms*R*(UINT64_C(1)<<(R-1)):0;
    for(unsigned t=0;t<j->m && ok;t++) {
        Worker *w=&j->w[t];w->prefix=u64in(&reader);w->states=u64in(&reader);w->transitions=u64in(&reader);uint64_t layer=u64in(&reader),active=u64in(&reader);w->len=u64in(&reader);w->pos=u64in(&reader);uint64_t cap=u64in(&reader),used=u64in(&reader);
        if(w->states>work_bound || w->transitions>transition_bound || !reader.ok || layer>j->N || active>1 || w->prefix>j->atoms+j->m || w->prefix%j->m!=t || w->pos>w->len || (active && w->prefix>=j->atoms) || (!active && (w->len || cap || used)) || (active && (layer<j->d || !w->len)) || (cap && (cap<16 || (cap&(cap-1)))) || used>(cap/10)*7+(cap%10)*7/10) {ok=false;break;}
        w->layer=(unsigned)layer;w->active=(unsigned)active;
        unsigned k=w->layer>=j->d?w->layer-j->d:0;
        uint64_t B=choose(j->N+3,3),L=B*choose(j->N-j->d,k),T=(w->layer<j->N)?B*choose(j->N-j->d,k+1):0;
        if(w->len>L || used>T || cap>tablecap(T) || w->len>j->snap_bound/24) {ok=false;break;}
        w->F=getmem(16*j->masks);if(!w->F) {ok=false;break;}
        for(uint64_t s=0;s<j->masks && ok;s++) {w->F[s]=u128in(&reader);if(!reader.ok || w->F[s]>factorial[__builtin_popcountll(s)] || (j->phase>=2 && t==0 && !w->F[s])) ok=false;}
        if(w->len) {w->cur=getmem(24*w->len);if(!w->cur) {ok=false;break;}}
        for(uint64_t i=0;i<w->len && ok;i++) {w->cur[i]=recin(&reader);if(!valid_rec(j,w->cur[i],w->layer) || (i && w->cur[i-1].key>=w->cur[i].key)) ok=false;}
        if(cap && !table_init(&w->next,cap)) ok=false;
        for(uint64_t i=0;i<used && ok;i++) {Rec r=recin(&reader);if(!valid_rec(j,r,w->layer+1) || !raw_insert(&w->next,r,true)) ok=false;}
    }
    uint64_t total_states=0,total_transitions=0;
    for(unsigned t=0;t<j->m && ok;t++) if(!count64(&total_states,j->w[t].states) || !count64(&total_transitions,j->w[t].transitions)) ok=false;
    if(total_states>work_bound || total_transitions>transition_bound) ok=false;
    struct stat st;if(!reader.ok || fstat(fd,&st) || st.st_size<32 || reader.consumed!=(uint64_t)st.st_size-32) ok=false;
    if(j->phase==0 && (j->reduce_worker!=1 || j->redpos || j->out_n!=1 || j->convpos || j->convsum)) ok=false;
    if(j->phase==1 && (j->out_n!=1 || j->convpos || j->convsum)) ok=false;
    if(j->phase>=1) for(unsigned t=0;t<j->m;t++) if(j->w[t].active || j->w[t].prefix<j->atoms) ok=false;
    if(j->phase>=2 && (j->reduce_worker!=j->m || j->redpos)) ok=false;
    if(j->phase==3 && (j->out_n!=j->M+1 || j->convpos || j->convsum)) ok=false;
    if(ok && j->phase==2 && (j->out_n>j->M || (j->out_n==1 && j->convpos) || (j->out_n>1 && j->convpos>=(UINT64_C(1)<<(j->out_n-2))))) ok=false;
    /* Every reduced F entry is positive: each consumed product is >=1. */
    if(j->phase==2 && ((!j->convpos && j->convsum) || j->convsum<j->convpos)) ok=false;
    if(close(fd)) ok=false;
    return ok;
}
static void config(Job *j,char out[512]) {snprintf(out,512,"{\"schema\":2,\"M\":%u,\"workers\":%u,\"depth\":%u,\"source\":\"%s\",\"makefile\":\"%s\",\"binary\":\"%s\"}\n",j->M,j->m,j->d,SOURCE_SHA,MAKE_SHA,binary_hex);}
static bool readconfig(int dir,Job *j,bool check) {
    int fd=regular(dir,"run.json",O_RDONLY);if(fd<0) return false;char buf[512]={0};ssize_t n=read(fd,buf,511);char extra;bool ok=n>0 && read(fd,&extra,1)==0;close(fd);if(!ok) return false;
    unsigned vals[3]={0};const unsigned maxima[3]={24,8,4};
    const char *labels[3]={"{\"schema\":2,\"M\":",",\"workers\":",",\"depth\":"};
    const char *cursor=buf;
    for(unsigned i=0;i<3;i++) {
        size_t k=strlen(labels[i]);if(strncmp(cursor,labels[i],k)) return false;cursor+=k;
        unsigned x=0,ndigits=0;
        while(*cursor>='0' && *cursor<='9') {
            unsigned digit=(unsigned)(*cursor-'0');
            if(digit>maxima[i] || x>(maxima[i]-digit)/10U || ++ndigits>2) return false;
            x=x*10+digit;cursor++;
        }
        if(!ndigits) return false;
        vals[i]=x;
    }
    unsigned M=vals[0],m=vals[1],d=vals[2];
    if(!bounds(M,m,d,&j->mem_bound,&j->snap_bound)) return false;
    if(check) {j->M=M;j->m=m;j->d=d;}else if(M!=j->M || m!=j->m || d!=j->d) return false;
    char expected[512];config(j,expected);return (size_t)n==strlen(expected) && !memcmp(buf,expected,(size_t)n);
}
static bool output(Job *j,int dir,bool verify) {
    char out[2048];size_t used=0;
    if(j->phase==3) {
        static const uint64_t known[]={0,1,2,4,8,16,34,82,252,890,3644,15390,67646,301210,1397898,6786792,35154332};
        for(unsigned n=1;n<=j->M;n++) {
            if(n<=16 && j->result[n]!=known[n]) return false;
            char dec[40];decimal(j->result[n],dec);int z=snprintf(out+used,sizeof(out)-used,"%u\t%s\n",n,dec);if(z<0 || (size_t)z>=sizeof(out)-used) return false;used+=(size_t)z;
        }
    }
    out[used]=0;
    if(!verify) return textfile(dir,"res.tsv",out,false);
    int fd=regular(dir,"res.tsv",O_RDONLY);if(fd<0) return false;char buf[2049];ssize_t n=read(fd,buf,sizeof(buf));close(fd);return n>=0 && (size_t)n==used && !memcmp(buf,out,used);
}
static bool manifest(int dir,bool verify) {
    char out[1024];size_t used=0;
    for(unsigned i=0;i<8;i++) {
        if(i==3 || i==5 || i==6 || i==7) continue; /* log/lock are not scientific receipts */
        int fd=regular(dir,names[i],O_RDONLY);if(fd<0) {if(errno==ENOENT) continue;return false;}
        struct stat st;unsigned char digest[32];bool ok=fstat(fd,&st)==0 && st.st_size>=0 && hashfd(fd,(uint64_t)st.st_size,digest);close(fd);if(!ok) return false;
        char h[65];hex(digest,h);int z=snprintf(out+used,sizeof(out)-used,"%s  %s\n",h,names[i]);if(z<0 || (size_t)z>=sizeof(out)-used) return false;used+=(size_t)z;
    }
    if(!verify) return textfile(dir,"sha.txt",out,false);
    int fd=regular(dir,"sha.txt",O_RDONLY);if(fd<0) return false;
    char buf[1025];ssize_t n=read(fd,buf,sizeof(buf));close(fd);
    return n>=0 && (size_t)n==used && !memcmp(buf,out,used);
}
static bool event(Job *j,int dir,const char *reason,double elapsed) {
    char line[1024];uint64_t states=0,tr=0;for(unsigned t=0;t<j->m;t++) {if(!count64(&states,j->w[t].states) || !count64(&tr,j->w[t].transitions)) return false;}
    snprintf(line,sizeof(line),"M=%u invocation=%"PRIu64" phase=%u generation=%"PRIu64" workers=%u states=%"PRIu64" transitions=%"PRIu64" requested_seconds=%.17g service_seconds=%.17g cut_elapsed_seconds=%.17g elapsed_before_receipt=%.17g allocated=%"PRIu64" peak=%"PRIu64" stop=%s remaining=UNKNOWN\n",j->M,j->invocations,j->phase,j->generation,j->m,states,tr,j->invocation_limit,j->invocation_service,j->cut_elapsed,elapsed,atomic_load(&allocated),atomic_load(&highwater),reason);
    return textfile(dir,"log.txt",line,false); /* bounded latest durable invocation receipt */
}
static void telemetry(Job *j,double elapsed,double service,double seconds,const char *reason) {
    fprintf(stderr,"M=%u invocation=%"PRIu64" phase=%u committed_gen=%"PRIu64" workers=%u elapsed=%.3f budget_left=%.3f alloc=%"PRIu64" peak=%"PRIu64" stop=%s residual=UNKNOWN\n",j->M,j->invocations,j->phase,j->generation,j->m,elapsed,seconds>service?seconds-service:0,atomic_load(&allocated),atomic_load(&highwater),reason);
    uint64_t states=0,tr=0;for(unsigned t=0;t<j->m;t++) {states+=j->w[t].states;tr+=j->w[t].transitions;}
    fprintf(stderr," service=%.6f actual_workers=%u actual_workers_valid=%u local_states=%"PRIu64" local_transitions=%"PRIu64"\n",service,j->actual_workers,j->actual_workers!=0,states-j->start_states,tr-j->start_transitions);
    for(unsigned t=0;t<j->m;t++) {Worker *w=&j->w[t];fprintf(stderr," worker=%u prefix=%"PRIu64"/%"PRIu64" active=%u layer=%u cursor=%"PRIu64"/%"PRIu64" states=%"PRIu64" transitions=%"PRIu64"\n",t,w->prefix,j->atoms,w->active,w->layer,w->pos,w->len,w->states,w->transitions);}
}
static bool uintarg(const char *s,unsigned max,unsigned *v) {if(!*s) return false;uint64_t x=0;for(;*s;s++) {if(*s<'0'||*s>'9' || x>(max-(unsigned)(*s-'0'))/10U || (unsigned)(*s-'0')>max) return false;x=x*10+(unsigned)(*s-'0');}*v=(unsigned)x;return true;}
static bool timearg(const char *s,double *v) {bool dot=false,digit=false;for(const char *p=s;*p;p++) {if(*p=='.' && !dot) dot=true;else if(*p>='0' && *p<='9') digit=true;else return false;}if(!digit) return false;errno=0;char *e;double x=strtod(s,&e);if(errno || *e || !isfinite(x) || x<=0 || x>3000) return false;*v=x;return true;}
static void usage(void) {fputs("a180207 next --root DIR --max M --workers W --depth D --seconds S\na180207 check --root DIR\nM=1..24; W=1..8; D=0..min(4,M-1); resource-admitted pairs only.\nS is useful invocation seconds, positive decimal <=3000, excluding save/load.\nSame next configuration resumes; new root/configuration for larger horizons.\nA failed initial creation may leave an unusable root; preserve it and use a new root.\nPartial recovery with nonempty res.tsv is refused without modifying artifacts.\nExit: 0 COMPLETE/valid check, 10 PARTIAL, 2 INVALID, 3 RESOURCE_OR_IO, 4 INTERNAL.\n",stderr);}
#ifndef A180207_DIAGNOSTICS
int main(int argc,char **argv) {
    if(argc==2 && !strcmp(argv[1],"--help")) {usage();return 0;}
    if(argc<2 || (strcmp(argv[1],"next") && strcmp(argv[1],"check"))) {usage();return 2;}
    bool checking=!strcmp(argv[1],"check");Job *j=NULL;void *jp=NULL;if(posix_memalign(&jp,64,sizeof(Job))) return 3;j=jp;memset(j,0,sizeof(*j));
    const char *root=NULL;double seconds=0;unsigned seen=0;
    for(int i=2;i<argc;i+=2) {
        if(i+1>=argc) {free(j);usage();return 2;}unsigned flag=0;const char *s=argv[i],*v=argv[i+1];bool ok=true;
        if(!strcmp(s,"--root")) {flag=1;root=v;ok=*v!=0;}
        else if(!strcmp(s,"--max")) {flag=2;ok=uintarg(v,24,&j->M) && j->M>0;}
        else if(!strcmp(s,"--workers")) {flag=4;ok=uintarg(v,8,&j->m) && j->m>0;}
        else if(!strcmp(s,"--depth")) {flag=8;ok=uintarg(v,4,&j->d);}
        else if(!strcmp(s,"--seconds")) {flag=16;ok=timearg(v,&seconds);}
        if(!flag || (seen&flag) || !ok) {message("invalid, duplicate or unknown argument");free(j);return 2;}seen|=flag;
    }
    if(seen!=(checking?1U:31U) || (!checking && !bounds(j->M,j->m,j->d,&j->mem_bound,&j->snap_bound))) {usage();free(j);return 2;}
    if(strlen(SOURCE_SHA)!=64 || strlen(MAKE_SHA)!=64) {message("unbound build; use canonical Makefile");free(j);return 2;}
    int exe=open("/proc/self/exe",O_RDONLY|O_CLOEXEC);struct stat st;unsigned char digest[32];bool hashed=exe>=0 && fstat(exe,&st)==0 && st.st_size>0 && hashfd(exe,(uint64_t)st.st_size,digest);if(exe>=0) close(exe);if(!hashed) {free(j);return 3;}hex(digest,binary_hex);
    bool fresh=false;
    int dir=open_root(root,checking,&fresh);
    if(dir<0) {int e=errno;perror("root/parent durability");free(j);return (e==EINVAL || e==ENAMETOOLONG || e==ENOTDIR || e==ELOOP || e==ENOENT)?2:3;}
    uint64_t live=0;if(!inventory(dir,&live)) {message("foreign files/type or quota violation");close(dir);free(j);return 2;}
    int lock=regular(dir,"lock",checking?O_RDONLY:(O_RDWR|O_CREAT));if(lock<0 || flock(lock,LOCK_EX|LOCK_NB)) {message("lock unavailable");if(lock>=0) close(lock);close(dir);free(j);return 2;}
    int rc=3;double start=now();
    if(fresh) {
        char cfg[512];config(j,cfg);if(!textfile(dir,"run.json",cfg,true)) goto finish;
        j->N=j->M-1;j->masks=UINT64_C(1)<<j->N;j->atoms=choose(j->N,j->d);init_math(j->N);
        if(!new_job(j) || !save(j,dir)) goto finish;
    } else {
        if(!readconfig(dir,j,checking)) {message("invalid or foreign immutable run.json");rc=2;goto finish;}
        j->N=j->M-1;j->masks=UINT64_C(1)<<j->N;j->atoms=choose(j->N,j->d);init_math(j->N);
        uint64_t g0=0,g1=0;int a=inspect(dir,"chk0.bin",j,&g0),b=inspect(dir,"chk1.bin",j,&g1);
        if(a==2 || b==2 || (a!=1 && b!=1) || (a==1 && b==1 && g0==g1)) {message("foreign or no valid checkpoint generations");rc=2;goto finish;}
        if(a==0 || b==0) message("CORRUPTION: using other validated generation; damaged generation retained until next commit");
        const char *best=(a==1 && (b!=1 || g0>g1))?"chk0.bin":"chk1.bin";
        if(!load(j,dir,best)) {message("invalid checkpoint state/length");rc=2;goto finish;}
        if(!checking) {
            struct stat result;
            if(!fstatat(dir,"res.tsv",&result,AT_SYMLINK_NOFOLLOW)) {
                if(j->phase<3 && result.st_size>0) {message("partial recovery would replace nonempty res.tsv; artifacts preserved; recover a complete generation or use a new root");rc=2;goto finish;}
            } else if(errno!=ENOENT) goto finish;
            struct stat temp;if(!fstatat(dir,"chk.tmp",&temp,AT_SYMLINK_NOFOLLOW)) {message("discarding uncommitted chk.tmp after valid-generation recovery");if(unlinkat(dir,"chk.tmp",0) || fsync(dir)) goto finish;}
        }
    }
    if(checking) {if(!output(j,dir,true) || !manifest(dir,true)) {message("derived res.tsv/sha.txt missing or inconsistent; inspect before next (partial recovery refuses nonempty res.tsv)");rc=2;}else {telemetry(j,now()-start,0,0,"VALID");rc=0;}goto finish;}
    if(j->generation>=UINT64_MAX-1) {message("checkpoint generation exhausted; state unchanged");rc=2;goto finish;}
    if(!count64(&j->invocations,1)) {rc=4;goto finish;}
    j->invocation_limit=seconds;j->invocation_service=0;j->cut_elapsed=now()-start;
    if(!output(j,dir,false) || !event(j,dir,"START_UNCOMMITTED",now()-start)) goto finish;
    omp_set_dynamic(0);struct sigaction sa;memset(&sa,0,sizeof(sa));sa.sa_handler=onsignal;sigemptyset(&sa.sa_mask);if(sigaction(SIGTERM,&sa,NULL) || sigaction(SIGINT,&sa,NULL)) goto finish;
    for(unsigned t=0;t<j->m;t++) {j->start_states+=j->w[t].states;j->start_transitions+=j->w[t].transitions;}
    double service=0,checkpoint_service=0,beat=now();
    telemetry(j,now()-start,service,seconds,"START");
    while(j->phase<3 && !stopping && service<seconds) {
        double tick=now();
        if(!advance(j)) {message("resource/numeric invariant failure; no mutated state committed");goto finish;}
        double t=now();service+=t-tick;if(t-beat>=30) {telemetry(j,t-start,service,seconds,"HEARTBEAT");beat=t;}
        if(service-checkpoint_service>=600 && j->phase<3) {
            j->invocation_service=service;j->cut_elapsed=now()-start;
            if(!save(j,dir) || !event(j,dir,"CHECKPOINT",now()-start)) goto finish;
            checkpoint_service=service;
        }
    }
    j->invocation_service=service;j->cut_elapsed=now()-start;
    if(!save(j,dir) || !output(j,dir,false) || !event(j,dir,stopping?"SIGNAL":(j->phase==3?"COMPLETE":"TIME_BUDGET"),now()-start) || !manifest(dir,false)) goto finish;
    telemetry(j,now()-start,service,seconds,j->phase==3?"COMPLETE":(stopping?"SIGNAL":"TIME_BUDGET"));rc=j->phase==3?0:10;
finish:
    if(rc==3) message("RESOURCE_OR_IO: stop; last durable generation preserved; no automatic retry");
    cleanup(j);close(lock);close(dir);free(j);return rc;
}
#endif
