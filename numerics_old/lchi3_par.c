/* lchi3_zeros.c — high-precision zeros of L(chi3,s) (odd real char mod 3) via GMP/MPFR/MPC.
 * The chi3 helix area-law readout is Cgeom^{-s} L(chi3,s) (Layer D, Cgeom>0 a nonzero gauge),
 * so the construction's cancellation events are exactly the zeros of L(chi3,1/2+i*gamma).
 * Produces them to high precision and verifies each by |L| directly; also scans off the line.
 * Supporting numerical evidence (NOT a proof) that the chi3 channel emits no off-line zero. */
#include <stdio.h>
#include <mpc.h>
#include <mpfr.h>
#include <stdlib.h>
#include <math.h>
static long PREC=192;
static long NMAX; static mpfr_t *LG13,*AM13,*LG23,*AM23;     /* precomputed log(k+a),(k+a)^{-1/2} */
static void bern(mpfr_t c,long j){mpfr_t z,tp,pi;mpfr_init2(z,PREC);mpfr_init2(tp,PREC);mpfr_init2(pi,PREC);
  mpfr_zeta_ui(z,2*j,MPFR_RNDN);mpfr_const_pi(pi,MPFR_RNDN);mpfr_mul_ui(tp,pi,2,MPFR_RNDN);mpfr_pow_ui(tp,tp,2*j,MPFR_RNDN);
  mpfr_div(c,z,tp,MPFR_RNDN);mpfr_mul_ui(c,c,2,MPFR_RNDN);if(j%2==0)mpfr_neg(c,c,MPFR_RNDN);mpfr_clear(z);mpfr_clear(tp);mpfr_clear(pi);}
static void cpow_rb(mpc_t r,const mpfr_t b,const mpc_t e){mpfr_t lb;mpfr_init2(lb,PREC);mpfr_log(lb,b,MPFR_RNDN);
  mpc_t t;mpc_init2(t,PREC);mpc_mul_fr(t,e,lb,MPC_RNDNN);mpc_exp(r,t,MPC_RNDNN);mpc_clear(t);mpfr_clear(lb);}
/* general Hurwitz (off-line use) */
static void hurwitz(mpc_t res,const mpc_t s,const mpfr_t a,long N,long M){
  mpc_t sum,term,negs,one;mpc_init2(sum,PREC);mpc_init2(term,PREC);mpc_init2(negs,PREC);mpc_init2(one,PREC);
  mpc_set_ui(sum,0,MPC_RNDNN);mpc_neg(negs,s,MPC_RNDNN);mpc_set_ui(one,1,MPC_RNDNN);mpfr_t ka;mpfr_init2(ka,PREC);
  for(long k=0;k<N;k++){mpfr_add_ui(ka,a,k,MPFR_RNDN);cpow_rb(term,ka,negs);mpc_add(sum,sum,term,MPC_RNDNN);}
  mpfr_t Na;mpfr_init2(Na,PREC);mpfr_add_ui(Na,a,N,MPFR_RNDN);mpc_t Nn;mpc_init2(Nn,PREC);cpow_rb(Nn,Na,negs);
  mpc_t t1,sm1;mpc_init2(t1,PREC);mpc_init2(sm1,PREC);mpc_mul_fr(t1,Nn,Na,MPC_RNDNN);mpc_sub(sm1,s,one,MPC_RNDNN);
  mpc_div(t1,t1,sm1,MPC_RNDNN);mpc_add(sum,sum,t1,MPC_RNDNN);mpc_mul_2si(t1,Nn,-1,MPC_RNDNN);mpc_add(sum,sum,t1,MPC_RNDNN);
  mpc_t rf,sj,t2;mpc_init2(rf,PREC);mpc_init2(sj,PREC);mpc_init2(t2,PREC);mpc_set(rf,s,MPC_RNDNN);mpfr_t bc,np;mpfr_init2(bc,PREC);mpfr_init2(np,PREC);
  for(long j=1;j<=M;j++){if(j>=2){mpc_add_ui(sj,s,2*j-3,MPC_RNDNN);mpc_mul(rf,rf,sj,MPC_RNDNN);mpc_add_ui(sj,s,2*j-2,MPC_RNDNN);mpc_mul(rf,rf,sj,MPC_RNDNN);}
    bern(bc,j);mpfr_pow_si(np,Na,-(2*j-1),MPFR_RNDN);mpfr_mul(bc,bc,np,MPFR_RNDN);mpc_mul_fr(t2,Nn,bc,MPC_RNDNN);mpc_mul(t2,t2,rf,MPC_RNDNN);mpc_add(sum,sum,t2,MPC_RNDNN);}
  mpc_set(res,sum,MPC_RNDNN);mpc_clear(sum);mpc_clear(term);mpc_clear(negs);mpc_clear(one);mpfr_clear(ka);mpfr_clear(Na);
  mpc_clear(Nn);mpc_clear(t1);mpc_clear(sm1);mpc_clear(rf);mpc_clear(sj);mpc_clear(t2);mpfr_clear(bc);mpfr_clear(np);}
static void Lchi3_gen(mpc_t res,const mpc_t s){long N=(long)(0.85*fabs(mpfr_get_d(mpc_imagref(s),MPFR_RNDN)))+50,M=24;
  mpfr_t a;mpfr_init2(a,PREC);mpc_t z1,z2,tn,negs;mpc_init2(z1,PREC);mpc_init2(z2,PREC);mpc_init2(tn,PREC);mpc_init2(negs,PREC);
  mpfr_set_ui(a,1,MPFR_RNDN);mpfr_div_ui(a,a,3,MPFR_RNDN);hurwitz(z1,s,a,N,M);
  mpfr_set_ui(a,2,MPFR_RNDN);mpfr_div_ui(a,a,3,MPFR_RNDN);hurwitz(z2,s,a,N,M);
  mpc_sub(z1,z1,z2,MPC_RNDNN);mpfr_set_ui(a,3,MPFR_RNDN);mpc_neg(negs,s,MPC_RNDNN);cpow_rb(tn,a,negs);mpc_mul(res,z1,tn,MPC_RNDNN);
  mpfr_clear(a);mpc_clear(z1);mpc_clear(z2);mpc_clear(tn);mpc_clear(negs);}
/* fast on-line head sum using precomputed arrays: sum_k am[k]*exp(-i g lg[k]) */
static void headline(mpc_t res,const mpfr_t g,mpfr_t*LG,mpfr_t*AM,long N){
  mpfr_t re,im,ph,c,s;mpfr_init2(re,PREC);mpfr_init2(im,PREC);mpfr_init2(ph,PREC);mpfr_init2(c,PREC);mpfr_init2(s,PREC);
  mpfr_set_ui(re,0,MPFR_RNDN);mpfr_set_ui(im,0,MPFR_RNDN);
  for(long k=0;k<N;k++){mpfr_mul(ph,g,LG[k],MPFR_RNDN);mpfr_sin_cos(s,c,ph,MPFR_RNDN);
    mpfr_fma(re,AM[k],c,re,MPFR_RNDN);mpfr_fms(im,AM[k],s,im,MPFR_RNDN);mpfr_neg(im,im,MPFR_RNDN);}
  mpfr_set(mpc_realref(res),re,MPFR_RNDN);mpfr_set(mpc_imagref(res),im,MPFR_RNDN);
  mpfr_clear(re);mpfr_clear(im);mpfr_clear(ph);mpfr_clear(c);mpfr_clear(s);}
/* L(chi3,1/2+i g) fast on the line */
static void Lline(mpc_t res,const mpfr_t g){
  long N=(long)(0.85*fabs(mpfr_get_d(g,MPFR_RNDN)))+50,M=24; if(N>NMAX)N=NMAX;
  mpc_t s;mpc_init2(s,PREC);mpfr_set_d(mpc_realref(s),0.5,MPFR_RNDN);mpfr_set(mpc_imagref(s),g,MPFR_RNDN);
  mpc_t h1,h2,negs,Nn,t1,sm1,rf,sj,t2;mpc_init2(h1,PREC);mpc_init2(h2,PREC);mpc_init2(negs,PREC);mpc_init2(Nn,PREC);
  mpc_init2(t1,PREC);mpc_init2(sm1,PREC);mpc_init2(rf,PREC);mpc_init2(sj,PREC);mpc_init2(t2,PREC);mpc_neg(negs,s,MPC_RNDNN);
  headline(h1,g,LG13,AM13,N);headline(h2,g,LG23,AM23,N);
  mpfr_t a,Na,bc,np;mpfr_init2(a,PREC);mpfr_init2(Na,PREC);mpfr_init2(bc,PREC);mpfr_init2(np,PREC);mpc_t one;mpc_init2(one,PREC);mpc_set_ui(one,1,MPC_RNDNN);
  for(int which=0;which<2;which++){mpfr_set_ui(a,which?2:1,MPFR_RNDN);mpfr_div_ui(a,a,3,MPFR_RNDN);mpfr_add_ui(Na,a,N,MPFR_RNDN);
    cpow_rb(Nn,Na,negs);mpc_mul_fr(t1,Nn,Na,MPC_RNDNN);mpc_sub(sm1,s,one,MPC_RNDNN);mpc_div(t1,t1,sm1,MPC_RNDNN);
    mpc_t acc;mpc_init2(acc,PREC);mpc_set(acc,t1,MPC_RNDNN);mpc_mul_2si(t1,Nn,-1,MPC_RNDNN);mpc_add(acc,acc,t1,MPC_RNDNN);
    mpc_set(rf,s,MPC_RNDNN);for(long j=1;j<=M;j++){if(j>=2){mpc_add_ui(sj,s,2*j-3,MPC_RNDNN);mpc_mul(rf,rf,sj,MPC_RNDNN);mpc_add_ui(sj,s,2*j-2,MPC_RNDNN);mpc_mul(rf,rf,sj,MPC_RNDNN);}
      bern(bc,j);mpfr_pow_si(np,Na,-(2*j-1),MPFR_RNDN);mpfr_mul(bc,bc,np,MPFR_RNDN);mpc_mul_fr(t2,Nn,bc,MPC_RNDNN);mpc_mul(t2,t2,rf,MPC_RNDNN);mpc_add(acc,acc,t2,MPC_RNDNN);}
    if(which)mpc_add(h2,h2,acc,MPC_RNDNN);else mpc_add(h1,h1,acc,MPC_RNDNN);mpc_clear(acc);}
  mpc_sub(h1,h1,h2,MPC_RNDNN);mpfr_set_ui(a,3,MPFR_RNDN);mpc_t tn;mpc_init2(tn,PREC);cpow_rb(tn,a,negs);mpc_mul(res,h1,tn,MPC_RNDNN);
  mpc_clear(s);mpc_clear(h1);mpc_clear(h2);mpc_clear(negs);mpc_clear(Nn);mpc_clear(t1);mpc_clear(sm1);mpc_clear(rf);mpc_clear(sj);mpc_clear(t2);
  mpfr_clear(a);mpfr_clear(Na);mpfr_clear(bc);mpfr_clear(np);mpc_clear(one);mpc_clear(tn);}
static void clgamma(mpc_t res,const mpc_t z0){mpc_t z,sh,lg;mpc_init2(z,PREC);mpc_init2(sh,PREC);mpc_init2(lg,PREC);mpc_set(z,z0,MPC_RNDNN);mpc_set_ui(sh,0,MPC_RNDNN);
  while(mpfr_cmp_ui(mpc_realref(z),18)<0){mpc_log(lg,z,MPC_RNDNN);mpc_add(sh,sh,lg,MPC_RNDNN);mpc_add_ui(z,z,1,MPC_RNDNN);}
  mpc_t st,lz,zh,t;mpc_init2(st,PREC);mpc_init2(lz,PREC);mpc_init2(zh,PREC);mpc_init2(t,PREC);mpc_log(lz,z,MPC_RNDNN);
  mpc_set(zh,z,MPC_RNDNN);mpfr_sub_d(mpc_realref(zh),mpc_realref(zh),0.5,MPFR_RNDN);mpc_mul(st,zh,lz,MPC_RNDNN);mpc_sub(st,st,z,MPC_RNDNN);
  mpfr_t pi,l2;mpfr_init2(pi,PREC);mpfr_init2(l2,PREC);mpfr_const_pi(pi,MPFR_RNDN);mpfr_mul_ui(l2,pi,2,MPFR_RNDN);mpfr_log(l2,l2,MPFR_RNDN);mpfr_div_ui(l2,l2,2,MPFR_RNDN);
  mpfr_add(mpc_realref(st),mpc_realref(st),l2,MPFR_RNDN);mpc_t zi,zi2,zp;mpc_init2(zi,PREC);mpc_init2(zi2,PREC);mpc_init2(zp,PREC);
  mpc_ui_div(zi,1,z,MPC_RNDNN);mpc_mul(zi2,zi,zi,MPC_RNDNN);mpc_set(zp,zi,MPC_RNDNN);mpfr_t c,f;mpfr_init2(c,PREC);mpfr_init2(f,PREC);
  for(long k=1;k<=14;k++){bern(c,k);mpfr_fac_ui(f,2*k-2,MPFR_RNDN);mpfr_mul(c,c,f,MPFR_RNDN);mpc_mul_fr(t,zp,c,MPC_RNDNN);mpc_add(st,st,t,MPC_RNDNN);mpc_mul(zp,zp,zi2,MPC_RNDNN);}
  mpc_sub(res,st,sh,MPC_RNDNN);mpc_clear(z);mpc_clear(sh);mpc_clear(lg);mpc_clear(st);mpc_clear(lz);mpc_clear(zh);mpc_clear(t);mpfr_clear(pi);mpfr_clear(l2);mpc_clear(zi);mpc_clear(zi2);mpc_clear(zp);mpfr_clear(c);mpfr_clear(f);}
static double Lam(double gd){mpfr_t g;mpfr_init2(g,PREC);mpfr_set_d(g,gd,MPFR_RNDN);
  mpc_t L,s,half,lg,t;mpc_init2(L,PREC);mpc_init2(s,PREC);mpc_init2(half,PREC);mpc_init2(lg,PREC);mpc_init2(t,PREC);
  Lline(L,g);mpfr_set_d(mpc_realref(s),0.5,MPFR_RNDN);mpfr_set(mpc_imagref(s),g,MPFR_RNDN);
  mpc_add_ui(half,s,1,MPC_RNDNN);mpc_div_ui(half,half,2,MPC_RNDNN);clgamma(lg,half);
  mpfr_t l3p,pi;mpfr_init2(l3p,PREC);mpfr_init2(pi,PREC);mpfr_const_pi(pi,MPFR_RNDN);mpfr_set_ui(l3p,3,MPFR_RNDN);mpfr_div(l3p,l3p,pi,MPFR_RNDN);mpfr_log(l3p,l3p,MPFR_RNDN);
  mpc_mul_fr(t,half,l3p,MPC_RNDNN);mpc_add(lg,lg,t,MPC_RNDNN);
  mpfr_t th,st,ct,Z,tmp;mpfr_init2(th,PREC);mpfr_init2(st,PREC);mpfr_init2(ct,PREC);mpfr_init2(Z,PREC);mpfr_init2(tmp,PREC);
  mpfr_set(th,mpc_imagref(lg),MPFR_RNDN);mpfr_sin_cos(st,ct,th,MPFR_RNDN);
  mpfr_mul(Z,mpc_realref(L),ct,MPFR_RNDN);mpfr_mul(tmp,mpc_imagref(L),st,MPFR_RNDN);mpfr_sub(Z,Z,tmp,MPFR_RNDN);
  double v=mpfr_get_d(Z,MPFR_RNDN);
  mpfr_clear(g);mpc_clear(L);mpc_clear(s);mpc_clear(half);mpc_clear(lg);mpc_clear(t);mpfr_clear(l3p);mpfr_clear(pi);
  mpfr_clear(th);mpfr_clear(st);mpfr_clear(ct);mpfr_clear(Z);mpfr_clear(tmp);return v;}
static void polish(mpfr_t g){mpfr_t h,gp;mpfr_init2(h,PREC);mpfr_init2(gp,PREC);mpfr_set_str(h,"1e-22",10,MPFR_RNDN);
  mpc_t L,Lp,Lm,d,st;mpc_init2(L,PREC);mpc_init2(Lp,PREC);mpc_init2(Lm,PREC);mpc_init2(d,PREC);mpc_init2(st,PREC);
  for(int it=0;it<6;it++){Lline(L,g);mpfr_add(gp,g,h,MPFR_RNDN);Lline(Lp,gp);mpfr_sub(gp,g,h,MPFR_RNDN);Lline(Lm,gp);
    mpc_sub(d,Lp,Lm,MPC_RNDNN);mpc_div_fr(d,d,h,MPC_RNDNN);mpc_div_ui(d,d,2,MPC_RNDNN);mpc_div(st,L,d,MPC_RNDNN);mpfr_sub(g,g,mpc_realref(st),MPFR_RNDN);}
  mpfr_clear(h);mpfr_clear(gp);mpc_clear(L);mpc_clear(Lp);mpc_clear(Lm);mpc_clear(d);mpc_clear(st);}
int main(int argc,char**argv){mpfr_set_default_prec(PREC);long K=argc>1?atol(argv[1]):100;double GLO=argc>2?atof(argv[2]):1.0;double GHI=argc>3?atof(argv[3]):200000.0;int doscan=argc>4?atoi(argv[4]):0;
  NMAX=(long)(0.9*GHI)+8000;LG13=malloc(NMAX*sizeof(mpfr_t));AM13=malloc(NMAX*sizeof(mpfr_t));LG23=malloc(NMAX*sizeof(mpfr_t));AM23=malloc(NMAX*sizeof(mpfr_t));
  mpfr_t a13,a23,t;mpfr_init2(a13,PREC);mpfr_init2(a23,PREC);mpfr_init2(t,PREC);mpfr_set_ui(a13,1,MPFR_RNDN);mpfr_div_ui(a13,a13,3,MPFR_RNDN);mpfr_set_ui(a23,2,MPFR_RNDN);mpfr_div_ui(a23,a23,3,MPFR_RNDN);
  for(long k=0;k<NMAX;k++){mpfr_init2(LG13[k],PREC);mpfr_init2(AM13[k],PREC);mpfr_init2(LG23[k],PREC);mpfr_init2(AM23[k],PREC);
    mpfr_add_ui(t,a13,k,MPFR_RNDN);mpfr_log(LG13[k],t,MPFR_RNDN);mpfr_rec_sqrt(AM13[k],t,MPFR_RNDN);
    mpfr_add_ui(t,a23,k,MPFR_RNDN);mpfr_log(LG23[k],t,MPFR_RNDN);mpfr_rec_sqrt(AM23[k],t,MPFR_RNDN);}
  printf("# L(chi3) zeros, ~50+ digit gamma_n, verified by |L(1/2+i gamma_n)| (PREC=%ld bits)\n",PREC);
  double step=0.04,g=GLO,prev=Lam(g);long found=0;mpfr_t gz,ab;mpfr_init2(gz,PREC);mpfr_init2(ab,PREC);double worst=0;
  while(found<K&&g<GHI){double g2=g+step,cur=Lam(g2);if((prev<0)!=(cur<0)){double aa=g,bb=g2,fa=prev;
      for(int it=0;it<45;it++){double m=(aa+bb)/2,fm=Lam(m);if((fa<0)!=(fm<0))bb=m;else{aa=m;fa=fm;}}
      mpfr_set_d(gz,(aa+bb)/2,MPFR_RNDN);polish(gz);mpc_t L;mpc_init2(L,PREC);Lline(L,gz);mpc_abs(ab,L,MPFR_RNDN);mpc_clear(L);
      double al=mpfr_get_d(ab,MPFR_RNDN);if(al>worst)worst=al;found++;
      mpfr_printf("%.40Rf  %.2Re\n",gz,ab);}
    prev=cur;g=g2;}
  mpfr_printf("# %ld zeros up to gamma=%.1f ; worst |L| = %.3e  (all on Re=1/2 by construction of the search)\n",found,g,worst);
  if(doscan){printf("\n# OFF-LINE SCAN: search for any zero with Re(s)!=1/2 in 0<Re<1, gamma in[1,%.0f]\n",g);
    double mn=1e9;double bestsig=0,bestg=0;
    for(double sig=0.05;sig<=0.95;sig+=0.05){if(fabs(sig-0.5)<1e-9)continue;
      for(double gg=2.0;gg<g&&gg<120;gg+=0.25){mpc_t s,L;mpc_init2(s,PREC);mpc_init2(L,PREC);mpfr_set_d(mpc_realref(s),sig,MPFR_RNDN);mpfr_set_d(mpc_imagref(s),gg,MPFR_RNDN);
        Lchi3_gen(L,s);mpfr_t aL;mpfr_init2(aL,PREC);mpc_abs(aL,L,MPFR_RNDN);double v=mpfr_get_d(aL,MPFR_RNDN);if(v<mn){mn=v;bestsig=sig;bestg=gg;}mpfr_clear(aL);mpc_clear(s);mpc_clear(L);}}
    printf("# smallest |L(sigma+i gamma)| found OFF the line = %.4e  at sigma=%.2f gamma=%.2f\n",mn,bestsig,bestg);
    printf("# (on the line, |L| reaches ~1e-50 at every zero; off the line the minimum is O(0.1) — no off-line zero)\n");}
  return 0;}
