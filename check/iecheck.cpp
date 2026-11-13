/* Exact repetition-allowed walk / inclusion-exclusion checker for A180207.
 * Copyright (c) 2026 Carlo Corti. No producer headers, state, or expected counts.
 * Bound and semantic proof: outputs/valid22/method.md. Serial C++17/Linux.
 */
#include <algorithm>
#include <array>
#include <charconv>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <iostream>
#include <string>
#include <sys/resource.h>
#include <vector>
__extension__ typedef unsigned __int128 U128;
__extension__ typedef __int128 S128;
static volatile std::sig_atomic_t interrupted=0;
static void stop(int) {interrupted=1;}
static std::string decimal(U128 x) {
    std::string s;
    do {s.push_back(static_cast<char>('0'+x%10));x/=10;} while(x);
    std::reverse(s.begin(),s.end());return s;
}
int main(int argc,char **argv) {
    unsigned n=0;
    if(argc!=2) return 2;
    const std::string text(argv[1]);const auto parsed=std::from_chars(text.data(),text.data()+text.size(),n);
    if(parsed.ec!=std::errc{} || parsed.ptr!=text.data()+text.size() || n<1 || n>22) return 2;
    std::signal(SIGTERM,stop);std::signal(SIGINT,stop);
    const auto start=std::chrono::steady_clock::now();const unsigned N=n-1;
    const unsigned width=N+1;
    std::vector<std::array<unsigned,3>> triples;
    std::vector<int> ids(width*width*width,-1);
    const auto ix=[width](unsigned a,unsigned b,unsigned c) {return (a*width+b)*width+c;};
    for(unsigned a=0;a<=N;++a) for(unsigned b=0;b<=N-a;++b) for(unsigned c=0;c<=N-a-b;++c) {
        ids[ix(a,b,c)]=static_cast<int>(triples.size());triples.push_back({a,b,c});
    }
    const std::size_t states=triples.size();
    const std::uint32_t subsets=UINT32_C(1)<<N,all=subsets-1;
    std::vector<std::uint16_t> next(states*width);
    std::vector<std::uint32_t> allowed(states);
    for(std::size_t i=0;i<states;++i) {
        const auto a=triples[i][0],b=triples[i][1],c=triples[i][2];const unsigned s=a+b+c,lower=std::max(1U,s);
        allowed[i]=lower<=N?all&~((UINT32_C(1)<<(lower-1))-1):0;
        for(unsigned v=lower;v<=N;++v) {
            const int destination=ids[ix(b,c,v-s)];
            if(destination<0 || static_cast<std::size_t>(destination)>=states) return 4;
            next[i*width+v]=static_cast<std::uint16_t>(destination);
        }
    }
    std::array<U128,22> powers{};powers[0]=1;
    for(unsigned h=1;h<=N;++h) powers[h]=powers[h-1]*N;
    const U128 piece_bound=powers[N]*(N+1);
    const U128 unsigned_bound=piece_bound*subsets;
    if(unsigned_bound>=(static_cast<U128>(1)<<127)) return 4;
    const S128 bound=static_cast<S128>(unsigned_bound);
    S128 answer=0;std::uint64_t visited=0;
    std::vector<U128> current(states),following(states);
    std::array<U128,22> L{};
    for(std::uint32_t T=0;T<subsets;++T) {
        if(interrupted) {std::cerr<<"INCOMPLETE_SIGNAL subsets="<<visited<<'\n';return 10;}
        std::fill(current.begin(),current.end(),0);current[0]=1;L.fill(0);L[0]=1;
        for(unsigned h=1;h<=N;++h) {
            std::fill(following.begin(),following.end(),0);U128 total=0;
            for(std::size_t i=0;i<states;++i) {
                const U128 weight=current[i];if(!weight) continue;
                std::uint32_t choices=T&allowed[i];
                total+=weight*static_cast<unsigned>(__builtin_popcount(choices));
                while(choices) {
                    const unsigned v=static_cast<unsigned>(__builtin_ctz(choices))+1;choices&=choices-1;
                    following[next[i*width+v]]+=weight;
                }
            }
            if(total>powers[h]) return 4;
            L[h]=total;current.swap(following);
        }
        U128 q=0;
        for(unsigned k=0;k<=N;++k) q+=L[k]*L[N-k];
        if(q>piece_bound) return 4;
        if((N-static_cast<unsigned>(__builtin_popcount(T)))&1U) answer-=static_cast<S128>(q);
        else answer+=static_cast<S128>(q);
        if(answer>bound || answer<-bound) return 4;
        ++visited;
        if(n>=18 && visited%65536==0) std::cerr<<"n="<<n<<" subsets="<<visited<<'/'<<subsets<<'\n';
    }
    U128 factorial=1;for(unsigned i=1;i<=n;++i) factorial*=i;
    if(answer<0 || static_cast<U128>(answer)>factorial || visited!=subsets) return 4;
    rusage ru{};if(getrusage(RUSAGE_SELF,&ru)) return 3;
    const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"{\"status\":\"COMPLETE\",\"method\":\"repetition_walk_inclusion_exclusion\",\"n\":"<<n
             <<",\"count\":\""<<decimal(static_cast<U128>(answer))<<"\",\"subsets\":"<<visited
             <<",\"expected_subsets\":"<<subsets<<",\"states\":"<<states<<",\"absolute_sum_bound\":\""<<decimal(unsigned_bound)
             <<"\",\"wall_seconds\":"<<seconds<<",\"rss_kib_linux\":"<<ru.ru_maxrss<<"}\n";
    return 0;
}
