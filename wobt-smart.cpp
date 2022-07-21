// Weird Odd BackTrack by Wenjie Fang (aka fwjmath) from Team China
// Licensed under GPLv3
// Contact: fwjmath -replace.these.words.by.at- gmail.com
// Only applicable to numbers strictly less than 2^64
// Only works on 64bit machines, where unsigned long int is of 64 bits

/* trn.c                 Thomas R. Nicely          2012.01.26.1000
 *
 * Freeware copyright (c) 2012 Thomas R. Nicely <http://www.trnicely.net>.
 * Released into the public domain by the author, who disclaims any legal
 * liability arising from its use. The routine iEvalExprMPZ is included
 * under the terms of the GNU GPL; see the header of that routine (at
 * the end of the code) for details.
 *
 * Trimmed by fwjmath, 2013.02.26
 */

// #define __USING_BOINC 1

// Using mingw stdio to fix issues on WinXP64
#define __USE_MINGW_ANSI_STDIO 1

#define _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <algorithm>
#include <vector>
#include <stdlib.h>
#include "gmp.h"
//#include "mpir.h"
#ifdef __USING_BOINC
#include "../boinc_api.h"
#include "../filesys.h"
#endif
//#include <boost/multiprecision/cpp_int.hpp>
//#include "trn.h"
#include <inttypes.h>

//#include <time.h>

#include <string.h>

#define INT32_MAX 2147483647L

int iMiller(mpz_t mpzN, long iB);
int iBPSW(mpz_t mpzN);
int iStrongLucasSelfridge(mpz_t mpzN);

unsigned long int ulDmax=0;
mpz_t mpzPseudoBarrier, mpzPseudoBarrierLarge, mpzPseudoBarrierException;

/**********************************************************************/
/**********************************************************************/
/*              Prime number generation and testing                   */
/**********************************************************************/
/**********************************************************************/
int iMiller(mpz_t mpzN, long iB)
{
/* Test N for primality using the Miller's strong probable prime
   test with base B. See Gary Miller's famous paper ("Riemann's
   hypothesis and tests for primality," Journal of Computation and
   System Science, 1976, Volume 13, pp 300-317).

   Returns 1 if N is a prime or a base-B strong probable prime.
   Returns 0 if N is definitely not a prime (composite or < 2).

   NOTE 1: Some will not regard this as a "pure" Miller's test with
   base B, since certain adjustments are made, prior to applying the
   algorithm, in order to work around invalid input values and
   improve performance:

   1) N < 3 and even N are screened out first.
   2) Multiples of the small primes (to qMax=# of binary digits in N)
      are returned as composite.
   3) Values of B < 2 are replaced by B=2.
   4) If N divides B exactly, B is replaced by B+1.

   If such adjustments are not made, a third return value (e.g., -1)
   must be allowed, indicating invalid input and an indeterminate result,
   and complicating the calling source code.

   NOTE 2: Not all authorities agree exactly on the conditions for
   Miller's test. Some allow B < 2 (Rosen, "Elementary number theory and
   its applications," 3rd ed., 1993, pp. 195-200), although there are good
   reasons to exclude such values. On the other hand, some require
   1 < B < N (Ribenboim, "The new book of prime number records,"
   3rd ed., 1996, pp. 113-116, 143-146). As far as I know, no one
   allows N to divide B, as this produces "false negatives"; e.g.,
   N=3 and B=6 fails Miller's test, thus indicating N=3 as composite.
   In practice, there appears to be no good reason to use any B < 2,
   and in fact its value is almost always chosen to be a small
   (positive) prime number. Furthermore, in my opinion, refusing to
   first screen out even values of N and N < 3 gratuitously adds
   unnecessary complication to the test.
*/

static long long iFirst=1;
static mpz_t mpzB, mpzNm1, mpzd, mpzRem, mpzSqrt;
long long iComp2, iBits, s, j, q, digits;
unsigned long int qMax;

/* Allocate the static variables used in Miller's test. */

if(iFirst)
  {
  mpz_init(mpzB);  /* Never needs more than one limb */
  iBits=mp_bits_per_limb*(1 + mpz_size(mpzN));
  if(iBits < 512)iBits=512;
  mpz_init2(mpzNm1, iBits);
  mpz_init2(mpzd, iBits);
  mpz_init2(mpzRem, 2*iBits);  /* must contain products */
  //if(!iPrime16Initialized)vGenPrimes16();
  iFirst=0;
  }

/* First take care of all N < 3 and all even N. */

//iComp2=mpz_cmp_si(mpzN, 2);
//if(iComp2 < 0)return(0);        /* N < 2 is by convention not prime */
//if(iComp2==0)return(1);         /* N=2 is prime */
//if(mpz_even_p(mpzN))return(0);  /* Even N > 2 is composite */

/* Try small prime divisors from 3 to an UB qMax determined by the size
   of N (qMax >= 31). */

//mpz_sqrt(mpzSqrt, mpzN);
//qMax=mpz_sizeinbase(mpzN, 2);  /* Number of binary digits in N */
//if(qMax < 36)qMax=36;
//j=2;  /* First trial divisor is 3, the second prime */
/*
while(1)
  {
  q=ulPrime16[j++];
  if(q > qMax)break;
  if(mpz_cmp_si(mpzN, q)==0)return(1);
  if(mpz_cmp_si(mpzSqrt, q) < 0)return(1);
  if(mpz_divisible_ui_p(mpzN, q))return(0);
  }
*/
/* Check for valid input. Miller's test requires B > 1, and N must not
   divide B exactly. Choose B=2 and B<--B+1 if these problems arise.
   This is technically a deviation from the pure Miller's test, but
   avoids the necessity of handling an error return of -1. */

if(iB < 2)iB=2;
mpz_set_si(mpzB, iB);
if(mpz_divisible_p(mpzB, mpzN))mpz_add_ui(mpzB, mpzB, 1);

/* Now compute d and s, where d is odd and N - 1 = (2^s)*d. */

mpz_sub_ui(mpzNm1, mpzN, 1);
s=mpz_scan1(mpzNm1, 0);
mpz_tdiv_q_2exp(mpzd, mpzNm1, s);

/* Now proceed with the Miller's algorithm. First, if B^d is
   congruent to 1 mod N, N is a strong probable prime to base B. */

mpz_powm(mpzRem, mpzB, mpzd, mpzN);
if(mpz_cmp_si(mpzRem, 1)==0)return(1);
if(s==0)return(0);

/* Now calculate B^((2^j)*d), for j=0,1,...,s-1 by successive
   squaring. If any of these is congruent to -1 mod N, N is a
   sprp base B. Start with j=0 and B^d, already computed.
   Miller's test uses repeated modular squaring in place of repeated
   modular exponentiation for speed (squaring is an order of
   magnitude faster). */

if(mpz_cmp(mpzRem, mpzNm1)==0)return(1);  /* j=0 case */
for(j=1; j < s; j++)
  {
  mpz_mul(mpzRem, mpzRem, mpzRem);
  mpz_mod(mpzRem, mpzRem, mpzN);
  if(mpz_cmp(mpzRem, mpzNm1)==0)return(1);
  }

return(0);
}
/**********************************************************************/
int iBPSW(mpz_t mpzN)
{
/* Returns 1 if N is a probable prime, that is, passes the primality
 * tests in this algorithm; in that case, N is prime, or a strong
 * Baillie-Pomerance-Selfridge-Wagstaff (Baillie-PSW or BPSW) pseudoprime
 * Returns 0 if N is definitely composite, or if N < 2.
 *
 * The strong Lucas-Selfridge test returns roughly 30 % as many
 * pseudoprimes as the standard test, at the price of an additiona
 * running time of roughly 10 %. Thus the strong Lucas-Selfridge test
 * appears to be more effective, and is the one employed here.
 *
 * Determines if N is a probable prime, using a version of the
 * algorithm outlined by Baillie, Pomerance, Selfridge, and Wagstaff
 * (ca. 1980). Values of N are tested successively as follows.
 *
 * (1) N < 2 is not prime. N=2 is prime. Even N > 2 are composite.
 * (2) Try small primes as trial divisors, up to qMax=the # of binary
 *     digits in N. This step is implicit here here as part of Miller's
 *     test.
 * (3) If there is small prime divisor, apply Miller's strong
 *     probable prime test with base 2. If N fails, it is definitely
 *     composite. If N passes, it is a prime or a strong pseudoprime
 *     to base 2.
 * (4) Apply the strong Lucas sequence test with Selfridge's parameters.
 *     If N fails the Lucas-Selfridge test, it is definitely composite
 *     (and a strong pseudoprime to base 2). If N passes the strong
 *     Lucas-Selfridge test, it is a strong Lucas probable prime (lprp),
 *     i.e., a prime or a strong Lucas-Selfridge pseudoprime.
 * (5) If N has passed all these tests, it is a strong BPSW probable
 *     prime---either prime, or a strong BPSW pseudoprime. In this event
 *     the relative frequency of primality is believed to be very close
 *     to 1, and possibly even equal to 1. With the aid of Pinch's tables
 *     of pseudoprimes, the author verified (May, 2005) that there exists
 *     no Baillie-PSW pseudoprime (either strong or standard) in N < 10^13.
 *     In January, 2007, with the aid of the present implementation and
 *     William Galway's table of pseudoprimes, Martin Fuller determined
 *     that no Baillie-PSW pseudoprime (standard or strong) exists for
 *     N < 10^15. More recently, using the author's code and a database of
 *     pseudoprimes prepared by Jan Feitsma, Jeff Gilchrist has determined
 *     (13 June 2009) that no Baillie-PSW pseudoprime (standard or strong)
 *     exists below 10^17. Furthermore, preliminary analysis by Gilchrist
 *     of Feitsma's database, further extended, indicates (24 October 2009)
 *     that no Baillie-PSW pseudoprime (standard or strong) exists below
 *     2^64 ~ 1.8446744e19 (double checking of this result is in progress).
 * (6) Note, however, that Carl Pomerance (1984) presented a heuristic
 *     argument that an infinite number of counterexamples exist to the
 *     standard BPSW test (and presumably to the strong BPSW test as well,
 *     based on similar reasoning), and even that (for sufficiently large x,
 *     dependent on t) the number of Baillie-PSW pseudoprimes < x exceeds
 *     x^(1-t), where t is an arbitrarily small pre-assigned positive number.
 *     Nevertheless, not a single Baillie-PSW pseudoprime has yet been found;
 *     consequently, the Baillie-PSW test carries an aura of dependability
 *     (justified or not) exceeding that of competing algorithms, such as
 *     multiple Miller's tests (the Miller-Rabin algorithm).
 *
 * In the unexpected event that no counterexample exists, this algorithm
 * (the strong BPSW test) would constitute a definitive fast certification
 * of primality with polynomial running time, O((log N)^3).
 *
 * References:
 *
 * o Arnault, Francois. The Rabin-Monier theorem for Lucas pseudoprimes.
 *   Math. Comp. 66 (1997) 869-881. See
 *   <http://www.unilim.fr/pages_perso/francois.arnault/publications.html>
 * o Baillie, Robert, and Samuel S. Wagstaff, Jr. Lucas pseudoprimes.
 *   Math. Comp. 35:152 (1980) 1391-1417. MR0583518 (81j:10005). See
 *   <http://mpqs.free.fr/LucasPseudoprimes.pdf>.
 * o Feitsma, Jan. The pseudoprimes below 10^16. June 2009. Available at
 *   <http://www.janfeitsma.nl/math/psp2/database>.
 * o Galway, William. The pseudoprimes below 10^15. 4 November 2002.
 *   Available at <http://oldweb.cecm.sfu.ca/pseudoprime/>.
 * o Gilchrist, Jeff. Pseudoprime enumeration with probabilistic
 *   primality tests. 13 June 2009. Available at
 *   <http://gilchrist.ca/jeff/factoring/pseudoprimes.htm>..
 * o Grantham, Jon. Frobenius pseudoprimes. Preprint (16 July 1998)
 *   available at <http://www.pseudoprime.com/pseudo1.ps>.
 * o Martin, Marcel. Re: Baillie-PSW - Which variant is correct?
 *   9 January 2004. See
 *   <http://groups.google.com/groups?hl=en&lr=&ie=UTF-8&oe=UTF-8&safe=off&selm=3FFF275C.2C6B5185%40ellipsa.no.sp.am.net>.
 * o Mo, Zhaiyu, and James P. Jones. A new primality test using Lucas
 *   sequences. Preprint (circa 1997).
 * o Pinch, Richard G. E. Pseudoprimes up to 10^13. 4th International
 *   Algorithmic Number Theory Symposium, ANTS-IV, Leiden, The
 *   Netherlands, 2--7 July 2000. Springer Lecture Notes in Computer
 *   Science 1838 (2000) 459-474. See
 *   <http://www.chalcedon.demon.co.uk/rgep/carpsp.html>.
 * o Pomerance, Carl. Are there counterexamples to the Baillie-PSW
 *   primality test? (1984) See <http://www.pseudoprime.com/dopo.pdf>.
 * o Pomerance, Carl, John L. Selfridge, and Samuel S. Wagstaff, Jr.
 *   The pseudoprimes to 25*10^9. Math. Comp. 35 (1980) 1003-1026. See
 *   <http://mpqs.free.fr/ThePseudoprimesTo25e9.pdf>.
 * o Ribenboim, Paulo. The new book of prime number records. 3rd ed.,
 *   Springer-Verlag, 1995/6, pp. 53-83, 126-132, 141-142 (note that on
 *   line 2, p. 142, "0 < r < s" should read "0 <= r < s").
 * o Weisstein, Eric W. Baillie-PSW primality test. See
 *   <http://mathworld.wolfram.com/Baillie-PSWPrimalityTest.html>.
 * o Weisstein, Eric W. Strong Lucas pseudoprime. See
 *   <http://mathworld.wolfram.com/StrongLucasPseudoprime.html>.
 *
 */

//int iComp2;

/* First eliminate all N < 3 and all even N. */
/*
iComp2=mpz_cmp_si(mpzN, 2);
if(iComp2 < 0)return(0);
if(iComp2==0)return(1);
if(mpz_even_p(mpzN))return(0);
*/
/* Carry out Miller's test with base 2. This will also carry
   out a check for small prime divisors. */

if(iMiller(mpzN, 2)==0)return(0);

// Lower than barrier, can apply pseudo-test
// On bases 2, 7, 61
if(0 > mpz_cmp(mpzN, mpzPseudoBarrier)){
	if(mpz_divisible_ui_p(mpzN, 7)) return 0;
	if(iMiller(mpzN, 7)==0) return 0;
	if(mpz_divisible_ui_p(mpzN, 61)) return 0;
	if(iMiller(mpzN, 61)==0) return 0;
	return 1;
}else if(0 > mpz_cmp(mpzN, mpzPseudoBarrierLarge)){
	if(iMiller(mpzN, 3)==0) return 0;
	if(iMiller(mpzN, 5)==0) return 0;
	if(iMiller(mpzN, 7)==0) return 0;
	if(0 == mpz_cmp(mpzN, mpzPseudoBarrierException)) return 0;
	return 1;
}

/* The rumored strategy of Mathematica could be imitated here by
 * performing additional Miller's tests. One could also carry out
 * one or more extra strong Lucas tests. See the routine iPrP for
 * an implementation.
 *
 * Now N is a prime, or a base-2 strong pseudoprime with no prime
 * divisor < 37. Apply the strong Lucas-Selfridge primality test.
 */

return(iStrongLucasSelfridge(mpzN));
}
/**********************************************************************/
int iStrongLucasSelfridge(mpz_t mpzN)
{
/* Test N for primality using the strong Lucas test with Selfridge's
   parameters. Returns 1 if N is prime or a strong Lucas-Selfridge
   pseudoprime (in which case N is also a pseudoprime to the standard
   Lucas-Selfridge test). Returns 0 if N is definitely composite.

   The running time of the strong Lucas-Selfridge test is, on average,
   roughly 10 % greater than the running time for the standard
   Lucas-Selfridge test (3 to 7 times that of a single Miller's test).
   However, the frequency of strong Lucas pseudoprimes appears to be
   only (roughly) 30 % that of (standard) Lucas pseudoprimes, and only
   slightly greater than the frequency of base-2 strong pseudoprimes,
   indicating that the strong Lucas-Selfridge test is more computationally
   effective than the standard version. */

int iComp2, iP, iJ, iSign;
long long lDabs, lD, lQ;
unsigned long int ulMaxBits, uldbits, ul, ulGCD, r, s;
mpz_t mpzU, mpzV, mpzNplus1, mpzU2m, mpzV2m, mpzQm, mpz2Qm,
      mpzT1, mpzT2, mpzT3, mpzT4, mpzD, mpzd, mpzQkd, mpz2Qkd;

#undef RETURN
#define RETURN(n)           \
  {                         \
  mpz_clear(mpzU);          \
  mpz_clear(mpzV);          \
  mpz_clear(mpzNplus1);     \
  mpz_clear(mpzU2m);        \
  mpz_clear(mpzV2m);        \
  mpz_clear(mpzQm);         \
  mpz_clear(mpz2Qm);        \
  mpz_clear(mpzT1);         \
  mpz_clear(mpzT2);         \
  mpz_clear(mpzT3);         \
  mpz_clear(mpzT4);         \
  mpz_clear(mpzD);          \
  mpz_clear(mpzd);          \
  mpz_clear(mpzQkd);        \
  mpz_clear(mpz2Qkd);       \
  return(n);                \
  }

/* This implementation of the algorithm assumes N is an odd integer > 2,
   so we first eliminate all N < 3 and all even N. As a practical matter,
   we also need to filter out all perfect square values of N, such as
   1093^2 (a base-2 strong pseudoprime); this is because we will later
   require an integer D for which Jacobi(D,N) = -1, and no such integer
   exists if N is a perfect square. The algorithm as written would
   still eventually return zero in this case, but would require
   nearly sqrt(N)/2 iterations. */

iComp2=mpz_cmp_si(mpzN, 2);
if(iComp2 < 0)return(0);
if(iComp2==0)return(1);
if(mpz_even_p(mpzN))return(0);
if(mpz_perfect_square_p(mpzN))return(0);

/* Allocate storage for the mpz_t variables. Most require twice
   the storage of mpzN, since multiplications of order O(mpzN)*O(mpzN)
   will be performed. */

ulMaxBits=2*mpz_sizeinbase(mpzN, 2) + mp_bits_per_limb;
mpz_init2(mpzU, ulMaxBits);
mpz_init2(mpzV, ulMaxBits);
mpz_init2(mpzNplus1, ulMaxBits);
mpz_init2(mpzU2m, ulMaxBits);
mpz_init2(mpzV2m, ulMaxBits);
mpz_init2(mpzQm, ulMaxBits);
mpz_init2(mpz2Qm, ulMaxBits);
mpz_init2(mpzT1, ulMaxBits);
mpz_init2(mpzT2, ulMaxBits);
mpz_init2(mpzT3, ulMaxBits);
mpz_init2(mpzT4, ulMaxBits);
mpz_init(mpzD);
mpz_init2(mpzd, ulMaxBits);
mpz_init2(mpzQkd, ulMaxBits);
mpz_init2(mpz2Qkd, ulMaxBits);

/* Find the first element D in the sequence {5, -7, 9, -11, 13, ...}
   such that Jacobi(D,N) = -1 (Selfridge's algorithm). Theory
   indicates that, if N is not a perfect square, D will "nearly
   always" be "small." Just in case, an overflow trap for D is
   included. */

lDabs=5;
iSign=1;
while(1)
  {
  lD=iSign*lDabs;
  iSign = -iSign;
  ulGCD=mpz_gcd_ui(NULL, mpzN, lDabs);
  /* if 1 < GCD < N then N is composite with factor lDabs, and
     Jacobi(D,N) is technically undefined (but often returned
     as zero). */
  if((ulGCD > 1) && mpz_cmp_ui(mpzN, ulGCD) > 0)RETURN(0);
  mpz_set_si(mpzD, lD);
  iJ=mpz_jacobi(mpzD, mpzN);
  if(iJ==-1)break;
  lDabs += 2;
  if(lDabs >= 0){
	if((unsigned long int)lDabs > ulDmax){
		ulDmax=lDabs;  /* tracks global max of |D| */
	}
  }
  if(lDabs > INT32_MAX-2)
    {
    fprintf(stderr,
      "\n ERROR: D overflows signed long in Lucas-Selfridge test.");
    fprintf(stderr, "\n N=");
    mpz_out_str(stderr, 10, mpzN);
    fprintf(stderr, "\n |D|=%ld\n\n", lDabs);
	#ifdef __USING_BOINC
    boinc_finish(EXIT_FAILURE);
	#else
	exit(EXIT_FAILURE);
	#endif
    }
  }

iP=1;         /* Selfridge's choice */
lQ=(1-lD)/4;  /* Required so D = P*P - 4*Q */

/* NOTE: The conditions (a) N does not divide Q, and
   (b) D is square-free or not a perfect square, are included by
   some authors; e.g., "Prime numbers and computer methods for
   factorization," Hans Riesel (2nd ed., 1994, Birkhauser, Boston),
   p. 130. For this particular application of Lucas sequences,
   these conditions were found to be immaterial. */

/* Now calculate N - Jacobi(D,N) = N + 1 (even), and calculate the
   odd positive integer d and positive integer s for which
   N + 1 = 2^s*d (similar to the step for N - 1 in Miller's test).
   The strong Lucas-Selfridge test then returns N as a strong
   Lucas probable prime (slprp) if any of the following
   conditions is met: U_d=0, V_d=0, V_2d=0, V_4d=0, V_8d=0,
   V_16d=0, ..., etc., ending with V_{2^(s-1)*d}=V_{(N+1)/2}=0
   (all equalities mod N). Thus d is the highest index of U that
   must be computed (since V_2m is independent of U), compared
   to U_{N+1} for the standard Lucas-Selfridge test; and no
   index of V beyond (N+1)/2 is required, just as in the
   standard Lucas-Selfridge test. However, the quantity Q^d must
   be computed for use (if necessary) in the latter stages of
   the test. The result is that the strong Lucas-Selfridge test
   has a running time only slightly greater (order of 10 %) than
   that of the standard Lucas-Selfridge test, while producing
   only (roughly) 30 % as many pseudoprimes (and every strong
   Lucas pseudoprime is also a standard Lucas pseudoprime). Thus
   the evidence indicates that the strong Lucas-Selfridge test is
   more effective than the standard Lucas-Selfridge test, and a
   Baillie-PSW test based on the strong Lucas-Selfridge test
   should be more reliable. */


mpz_add_ui(mpzNplus1, mpzN, 1);
s=mpz_scan1(mpzNplus1, 0);
mpz_tdiv_q_2exp(mpzd, mpzNplus1, s);

/* We must now compute U_d and V_d. Since d is odd, the accumulated
   values U and V are initialized to U_1 and V_1 (if the target
   index were even, U and V would be initialized instead to U_0=0
   and V_0=2). The values of U_2m and V_2m are also initialized to
   U_1 and V_1; the FOR loop calculates in succession U_2 and V_2,
   U_4 and V_4, U_8 and V_8, etc. If the corresponding bits
   (1, 2, 3, ...) of t are on (the zero bit having been accounted
   for in the initialization of U and V), these values are then
   combined with the previous totals for U and V, using the
   composition formulas for addition of indices. */

mpz_set_ui(mpzU, 1);                      /* U=U_1 */
mpz_set_ui(mpzV, iP);                     /* V=V_1 */
mpz_set_ui(mpzU2m, 1);                    /* U_1 */
mpz_set_si(mpzV2m, iP);                   /* V_1 */
mpz_set_si(mpzQm, lQ);
mpz_set_si(mpz2Qm, 2*lQ);
mpz_set_si(mpzQkd, lQ);  /* Initializes calculation of Q^d */

uldbits=mpz_sizeinbase(mpzd, 2);
for(ul=1; ul < uldbits; ul++)  /* zero bit on, already accounted for */
  {
/* Formulas for doubling of indices (carried out mod N). Note that
 * the indices denoted as "2m" are actually powers of 2, specifically
 * 2^(ul-1) beginning each loop and 2^ul ending each loop.
 *
 * U_2m = U_m*V_m
 * V_2m = V_m*V_m - 2*Q^m
 */
  mpz_mul(mpzU2m, mpzU2m, mpzV2m);
  mpz_mod(mpzU2m, mpzU2m, mpzN);
  mpz_mul(mpzV2m, mpzV2m, mpzV2m);
  mpz_sub(mpzV2m, mpzV2m, mpz2Qm);
  mpz_mod(mpzV2m, mpzV2m, mpzN);
  /* Must calculate powers of Q for use in V_2m, also for Q^d later */
  mpz_mul(mpzQm, mpzQm, mpzQm);
  mpz_mod(mpzQm, mpzQm, mpzN);  /* prevents overflow */
  mpz_mul_2exp(mpz2Qm, mpzQm, 1);
  if(mpz_tstbit(mpzd, ul))
    {
/* Formulas for addition of indices (carried out mod N);
 *
 * U_(m+n) = (U_m*V_n + U_n*V_m)/2
 * V_(m+n) = (V_m*V_n + D*U_m*U_n)/2
 *
 * Be careful with division by 2 (mod N)!
 */
    mpz_mul(mpzT1, mpzU2m, mpzV);
    mpz_mul(mpzT2, mpzU, mpzV2m);
    mpz_mul(mpzT3, mpzV2m, mpzV);
    mpz_mul(mpzT4, mpzU2m, mpzU);
    mpz_mul_si(mpzT4, mpzT4, lD);
    mpz_add(mpzU, mpzT1, mpzT2);
    if(mpz_odd_p(mpzU))mpz_add(mpzU, mpzU, mpzN);
    mpz_fdiv_q_2exp(mpzU, mpzU, 1);
    mpz_add(mpzV, mpzT3, mpzT4);
    if(mpz_odd_p(mpzV))mpz_add(mpzV, mpzV, mpzN);
    mpz_fdiv_q_2exp(mpzV, mpzV, 1);
    mpz_mod(mpzU, mpzU, mpzN);
    mpz_mod(mpzV, mpzV, mpzN);
    mpz_mul(mpzQkd, mpzQkd, mpzQm);  /* Calculating Q^d for later use */
    mpz_mod(mpzQkd, mpzQkd, mpzN);
    }
  }

/* If U_d or V_d is congruent to 0 mod N, then N is a prime or a
   strong Lucas pseudoprime. */

if(mpz_sgn(mpzU)==0)RETURN(1);
if(mpz_sgn(mpzV)==0)RETURN(1);

/* NOTE: Ribenboim ("The new book of prime number records," 3rd ed.,
   1995/6) omits the condition V? on p.142, but includes it on
   p. 130. The condition is NECESSARY; otherwise the test will
   return false negatives---e.g., the primes 29 and 2000029 will be
   returned as composite. */

/* Otherwise, we must compute V_2d, V_4d, V_8d, ..., V_{2^(s-1)*d}
   by repeated use of the formula V_2m = V_m*V_m - 2*Q^m. If any of
   these are congruent to 0 mod N, then N is a prime or a strong
   Lucas pseudoprime. */

mpz_mul_2exp(mpz2Qkd, mpzQkd, 1);  /* Initialize 2*Q^(d*2^r) for V_2m */
for(r=1; r < s; r++)
  {
  mpz_mul(mpzV, mpzV, mpzV);
  mpz_sub(mpzV, mpzV, mpz2Qkd);
  mpz_mod(mpzV, mpzV, mpzN);
  if(mpz_sgn(mpzV)==0)RETURN(1);
/* Calculate Q^{d*2^r} for next r (final iteration irrelevant). */
  if(r < s-1)
    {
    mpz_mul(mpzQkd, mpzQkd, mpzQkd);
    mpz_mod(mpzQkd, mpzQkd, mpzN);
    mpz_mul_2exp(mpz2Qkd, mpzQkd, 1);
    }
  }

/* Otherwise N is definitely composite. */

RETURN(0);
}

// Starting
#define CKPTINT (1<<16)
// (1<<23)

using namespace std;

// Primes
// Since we are searching for odd numbers, we don't use 0th number, namely 2.
unsigned long int prime_cnt=5000000;
vector < unsigned long int > primes(5000000,0);
vector < unsigned long int > primeseg(1000,0);

// Search mechanism
mpz_t upperbound, lowerbound;
unsigned int slotptr;
unsigned long int factor[129]; // Actually we store the pointer of primes, and slot 0 is never used.
unsigned int multip[129];
unsigned long int factor_val[129];
unsigned long int next_factor[129];
mpz_t factored[129];
mpz_t residue[129];
mpz_t presum[129];
mpz_t factor_bound[129];

// General temporary variables. Do not use across recursive calls.
mpz_t gtmp, gtmp1, gtmp2, gtmp3, gtmp4, gtmp5;
mpz_t ltmp, ltmp1, ltmp2, ltmp3, ltmp4;

// Divisors array
#define DIVISOR_BOUND 1048576
unsigned __int128 divisors[DIVISOR_BOUND];
unsigned int divisor_cnt;

// IO
FILE* fio;

// Checkpoint, checksum
unsigned long int p_cnt;
unsigned long int workpoint, wp_res;
#define WORKPOINT_PERIOD 50000000 // 5e7
#define WORKPOINT_SEG 250
#define WORKPOINT_LIMIT 20000000000 // 2e10
unsigned long int primepoint, pp_res;
#define PRIMEPOINT_PERIOD 200000000 // 2e8
#define PRIMEPOINT_LIMIT 40000000000 // 4e10

// debug
unsigned long int checksum;

unsigned long int sec_num;

// production
unsigned long int SEC_CONST = 10000000000; // 1e10

unsigned long int excess_bound = 100000000000000; // 1e14

mpz_t cnv128tmp;
// assuming all values are lower than 2^128
__inline unsigned __int128 mpz_to_u128(mpz_t m){
	unsigned __int128 r;
	mpz_tdiv_q_2exp(cnv128tmp,m,64);
	r=mpz_get_ui(cnv128tmp);
	r<<=64;
	mpz_tdiv_r_2exp(cnv128tmp,m,64);
	r+=mpz_get_ui(cnv128tmp);
	return r;
}

// 1000000th prime is 15485863
// 5000000th prime is 86028121
// TODO : testing new bitmap approach
void primeSieve(){
	int* sieve;
	sieve=(int*)malloc(sizeof(int)*(1+(86028122>>5)));
	memset(sieve, 0, sizeof(int)*(1+(86028122>>5)));
	int ptr=2, s;
	int primeptr=0;
	while(true){
		s=(ptr<<1);
		while(s<86028122){
			sieve[(s>>5)]|=(1<<(s&31));
			s+=ptr;
		}
		sieve[ptr>>5]|=(1<<(ptr&31));
		primes[primeptr]=ptr;
		while((ptr<86028122)&&((sieve[(ptr>>5)]&(1<<(ptr&31)))!=0)) ptr++;
		if(ptr>=86028122) break;
		primeptr++;
	}
	free(sieve);
	s=4999;
	for(ptr=0;ptr<1000;ptr++){
		primeseg[ptr]=primes[s];
		s+=5000;
	}
	return;
}

__inline bool checkprime(mpz_t cand){
	if(0!=mpz_divisible_ui_p(cand,3)) return false;
	else if(0!=mpz_divisible_ui_p(cand,5)) return false;
	else if(0!=mpz_divisible_ui_p(cand,7)) return false;
	else if(0!=mpz_divisible_ui_p(cand,11)) return false;
	else if(0!=mpz_divisible_ui_p(cand,13)) return false;
	else return (iBPSW(gtmp3)!=0);
}

__inline unsigned long int getnextprime(unsigned long int ptr, unsigned long int curprime){
	if(ptr<prime_cnt-1){
		primepoint++;
		pp_res++;
		return primes[ptr+1];
	}else{
		unsigned long int tmp=curprime+2;
		mpz_set_ui(gtmp3,tmp);
		while(!checkprime(gtmp3)){ 
			tmp+=2; 
			mpz_set_ui(gtmp3,tmp);
			primepoint+=1; 
			pp_res+=1; 
		}
		return tmp;
	}
}

__inline unsigned long int getnextprime2(unsigned long int* ptr, unsigned long int curprime){
	if(curprime<86028121){
		// binary search for prime >= curprime
		// unsigned long int a=*ptr, c=primecnt-1;
		// unsigned long int b=(a+c)>>1;
		primepoint++;
		pp_res++;
		//unsigned long int a = *ptr;
		//while(primes[a] < curprime) a++;
		unsigned long int a=upper_bound(primeseg.begin(), primeseg.end(), curprime-1)-primeseg.begin();
		a*=5000;
		a=upper_bound(primes.begin()+a, primes.begin()+a+5000, curprime-1)-primes.begin();
		*ptr=a;
		return primes[a];
	}else{
		unsigned long int tmp=curprime;
		if((curprime&1)==0) tmp++;
		mpz_set_ui(gtmp3,tmp);
		while(!checkprime(gtmp3)){ 
			tmp+=2; 
			mpz_set_ui(gtmp3,tmp);
			primepoint+=1;
			pp_res+=1;
		}
		*ptr+=prime_cnt;
		return tmp;
	}
}

char buffer[4096];
unsigned int inp_sec_num;

__inline void get_inpprogress(){
	#ifdef __USING_BOINC
	string resolved_name;
	int retval = boinc_resolve_filename_s("inp.txt", resolved_name);
	if (retval) {printf("can't resolve filename"); boinc_finish(-1);}
	fio = boinc_fopen(resolved_name.c_str(), "r");
	#else
	fio=fopen("inp.txt","r");
	#endif
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fgets(buffer,4095,fio);
	fscanf(fio,"%u",&inp_sec_num);
	fclose(fio);
	return;
}

__inline bool border_cond(){
	mpz_pow_ui(gtmp5, factor_bound[slotptr-1], 2);
	mpz_mul_ui(gtmp5, gtmp5, SEC_CONST);
	if(mpz_cmp(residue[slotptr-1], gtmp5)>0) return false;
	mpz_pow_ui(gtmp5, factor_bound[slotptr-2], 2);
	mpz_mul_ui(gtmp5, gtmp5, SEC_CONST);
	return (mpz_cmp(residue[slotptr-1], gtmp5)<=0);
	//return ((residue[slotptr-1]<=factor_bound[slotptr-1]*factor_bound[slotptr-1]*SEC_CONST)&&(residue[slotptr-2]>factor_bound[slotptr-2]*factor_bound[slotptr-2]*SEC_CONST));
}

__inline void init(){
	unsigned long int wptemp=0;
	
	// Initialize pseudoprime barrier
	mpz_init(mpzPseudoBarrier);
	// Using value from primes.utm.edu
	// Check bases are 2, 7, 61
	mpz_set_str(mpzPseudoBarrier,"4759123140",10);
	mpz_set_str(mpzPseudoBarrierLarge,"118670087460",10);
	mpz_set_str(mpzPseudoBarrierException,"3215031751",10);
	
	// Initialize prime table
	primeSieve();
	
	// Initialize tables
	for(int i=0;i<129;i++){
		factor[i]=0;
		multip[i]=0;
		mpz_init(residue[i]);
		mpz_init(presum[i]);
		mpz_init(factored[i]);
		factor_val[i]=0;
		next_factor[i]=0;
		mpz_init(factor_bound[i]);
	}
	slotptr=1;
	mpz_set_ui(presum[0],1);
	mpz_set_ui(factored[0],1);
	next_factor[0]=3;
	p_cnt=0;
	workpoint=0;
	wp_res=0;
	primepoint=0;
	pp_res=0;
	checksum=0;
	sec_num=0;
	
	mpz_inits(upperbound,lowerbound,gtmp,gtmp1,gtmp2,gtmp3,gtmp4,gtmp5,ltmp,ltmp1,ltmp2,ltmp3,ltmp4,cnv128tmp,NULL);
	
	get_inpprogress();

	// Treat checkpoint file first
	#ifdef __USING_BOINC
	fio=boinc_fopen("ckpt.txt","r");
	#else
	fio=fopen("ckpt.txt","r");
	#endif
	if(fio!=NULL){
		gmp_fscanf(fio,"%Zd", upperbound);
		gmp_fscanf(fio,"%Zd", lowerbound);
		mpz_set(residue[0],upperbound);
		fscanf(fio,"%llu",&excess_bound);
		fscanf(fio,"%u",&slotptr);
		fscanf(fio,"%llu",&p_cnt);
		fscanf(fio,"%llu",&workpoint);
		fscanf(fio,"%llu",&primepoint);
		fscanf(fio,"%llu",&checksum);
		fscanf(fio,"%llu",&sec_num);
		wp_res=workpoint%WORKPOINT_PERIOD;
		pp_res=primepoint%PRIMEPOINT_PERIOD;
		wptemp=primepoint;
		for(unsigned int i=1; i<slotptr; i++){
			fscanf(fio,"%llu %u %llu",&factor[i],&multip[i],&factor_val[i]);
			mpz_set_ui(ltmp,factor_val[i]);
			mpz_set(ltmp1,ltmp);
			mpz_add_ui(ltmp2,ltmp,1);
			for(unsigned int j=1;j<multip[i];j++){
				//ltmp1*=ltmp;
				mpz_mul(ltmp1,ltmp1,ltmp);
				//ltmp2+=ltmp1;
				mpz_add(ltmp2,ltmp2,ltmp1);
			}
			//residue[i]=residue[i-1]/ltmp1;
			mpz_tdiv_q(residue[i],residue[i-1],ltmp1);
			//presum[i]=presum[i-1]*ltmp2;
			mpz_mul(presum[i],presum[i-1],ltmp2);
			//factored[i]=factored[i-1]*ltmp1;
			mpz_mul(factored[i],factored[i-1],ltmp1);
			next_factor[i]=getnextprime(factor[i], factor_val[i]);
			//gtmp4=factored[i];
			mpz_set(gtmp4,factored[i]);
			//gtmp4+=factored[i];
			mpz_add(gtmp4,gtmp4,factored[i]);
			//gtmp5=gtmp4;
			mpz_set(gtmp5,gtmp4);
			//gtmp5-=presum[i];
			mpz_sub(gtmp5,gtmp5,presum[i]);
			//gtmp4-=excess_bound+1;
			mpz_sub_ui(gtmp4,gtmp4,excess_bound+1);
			//gtmp4/=gtmp5;
			mpz_tdiv_q(gtmp4,gtmp4,gtmp5);
			//factor_bound[i]=gtmp4;
			mpz_set(factor_bound[i],gtmp4);
			next_factor[i]--;
			if(mpz_cmp_ui(factor_bound[i],next_factor[i])<0){
				mpz_set_ui(factor_bound[i],next_factor[i]);
			}
			next_factor[i]++;
			if(i>=2){
				unsigned int utmp=slotptr;
				slotptr=i+1;
				if(border_cond()) sec_num++;
				slotptr=utmp;
			}
		}
		fclose(fio);
		primepoint=wptemp;
		pp_res=primepoint%PRIMEPOINT_PERIOD;
	}else{
		// Read input file if no ckpt is available
		#ifdef __USING_BOINC
		string resolved_name;
		int retval = boinc_resolve_filename_s("inp.txt", resolved_name);
		if (retval) {printf("can't resolve filename"); boinc_finish(-1);}
		fio = boinc_fopen(resolved_name.c_str(), "r");
		#else
		fio=fopen("inp.txt","r");
		#endif
		gmp_fscanf(fio,"%Zd", upperbound);
		gmp_fscanf(fio,"%Zd", lowerbound);
		mpz_set(residue[0],upperbound);
		fscanf(fio,"%llu",&excess_bound);
		fscanf(fio,"%u",&slotptr);
		fscanf(fio,"%llu",&p_cnt);
		fscanf(fio,"%llu",&workpoint);
		fscanf(fio,"%llu",&primepoint);
		fscanf(fio,"%llu",&checksum);
		fscanf(fio,"%llu",&sec_num);
		wp_res=workpoint%WORKPOINT_PERIOD;
		pp_res=primepoint%PRIMEPOINT_PERIOD;
		wptemp=primepoint;
		for(unsigned int i=1; i<slotptr; i++){
			fscanf(fio,"%llu %u %llu",&factor[i],&multip[i],&factor_val[i]);
			mpz_set_ui(ltmp,factor_val[i]);
			mpz_set_ui(ltmp1,factor_val[i]);
			mpz_add_ui(ltmp2,ltmp,1);
			for(unsigned int j=1;j<multip[i];j++){
				mpz_mul(ltmp1,ltmp1,ltmp);
				mpz_add(ltmp2,ltmp2,ltmp1);
			}
			mpz_tdiv_q(residue[i],residue[i-1],ltmp1);
			mpz_mul(presum[i],presum[i-1],ltmp2);
			mpz_mul(factored[i],factored[i-1],ltmp1);
			next_factor[i]=getnextprime(factor[i], factor_val[i]);
			mpz_set(gtmp4,factored[i]);
			mpz_add(gtmp4,gtmp4,factored[i]);
			mpz_set(gtmp5,gtmp4);
			mpz_sub(gtmp5,gtmp5,presum[i]);
			mpz_sub_ui(gtmp4,gtmp4,excess_bound+1);
			mpz_tdiv_q(gtmp4,gtmp4,gtmp5);
			mpz_set(factor_bound[i],gtmp4);
			next_factor[i]--;
			if(mpz_cmp_ui(factor_bound[i],next_factor[i])<0){
				mpz_set_ui(factor_bound[i],next_factor[i]);
			}
			next_factor[i]++;
			if(i>=2){
				unsigned int utmp=slotptr;
				slotptr=i+1;
				if(border_cond()) sec_num++;
				slotptr=utmp;
			}
		}
		fclose(fio);
	}

	//sec_num++;
	
	mpz_set(gtmp5,factored[slotptr-1]);
	mpz_mul_2exp(gtmp5,gtmp5,1);
	if(mpz_cmp(gtmp5,presum[slotptr-1])<=0) slotptr--;
	
	// debug
	/*
	time_t tt;
	time(&tt);
	printf("Ckpt: %s", asctime(localtime(&tt)));
	fflush(stdout);
	*/
	// end debug
	
	return;
}

__inline void update_progress(){
	double frac1=1.0f-((double)sec_num/(double)inp_sec_num);
	double frac2=(double)workpoint/WORKPOINT_LIMIT;
	double frac3=(double)primepoint/PRIMEPOINT_LIMIT;
	if(frac1>1.0f) frac1=1.0f;
	if(frac1<0.0f) frac1=0.0f;
	if(frac2>1.0f) frac2=1.0f;
	if(frac2<0.0f) frac2=0.0f;
	if(frac3>1.0f) frac3=1.0f;
	if(frac3<0.0f) frac3=0.0f;
	#ifndef __USING_BOINC
	fio=fopen("fraction.txt","w");
	#endif
	if(frac1<frac2) frac1=frac2;
	if(frac1<frac3) frac1=frac3;
	#ifndef __USING_BOINC
	fprintf(fio,"%.5f",frac1);
	fclose(fio);
	#else
	boinc_fraction_done(frac1);
	#endif
	return;
}

// Contract: the slot slotptr must be the first empty slot
__inline void checkpoint(){
	#ifdef __USING_BOINC
	if(boinc_time_to_checkpoint()) {
		fio=boinc_fopen("ckpt.txt","wb");
		gmp_fprintf(fio,"%Zd%c", upperbound, 10);
		gmp_fprintf(fio,"%Zd%c", lowerbound, 10);
		fprintf(fio,"%llu%c",excess_bound, 10);
		fprintf(fio, "%u%c", slotptr, 10);
		fprintf(fio, "%llu%c", p_cnt, 10);
		fprintf(fio, "%llu%c", workpoint, 10);
		fprintf(fio, "%llu%c", primepoint, 10);
		fprintf(fio, "%llu%c", checksum, 10);
		fprintf(fio, "%llu%c", sec_num, 10);
		for(unsigned int i=1; i<slotptr; i++) fprintf(fio, "%llu %u %llu%c", factor[i], multip[i], factor_val[i], 10);
		fclose(fio);
		boinc_checkpoint_completed();
	}
	#else
	fio=fopen("ckpt.txt","wb");
	gmp_fprintf(fio,"%Zd%c", upperbound, 10);
	gmp_fprintf(fio,"%Zd%c", lowerbound, 10);
	fprintf(fio,"%llu%c",excess_bound, 10);
	fprintf(fio, "%u%c", slotptr, 10);
	fprintf(fio, "%llu%c", p_cnt, 10);
	fprintf(fio, "%llu%c", workpoint, 10);
	fprintf(fio, "%llu%c", primepoint, 10);
	fprintf(fio, "%llu%c", checksum, 10);
	fprintf(fio, "%llu%c", sec_num, 10);
	for(unsigned int i=1; i<slotptr; i++) fprintf(fio, "%llu %u %llu%c", factor[i], multip[i], factor_val[i], 10);
	fclose(fio);
	#endif
	// debug
	/*
	time_t tt;
	time(&tt);
	printf("Ckpt: %s", asctime(localtime(&tt)));
	fflush(stdout);
	*/
	// end debug
	update_progress();
	return;
}

// For debug
void print_factors(){
	//char c;
	gmp_printf("Sector %llu^%d", factor_val[1], multip[1]);
	for(unsigned int i=2;i<slotptr;i++) gmp_printf(" * %llu^%d", factor_val[i], multip[i]);
	printf("\n");
	return;
}

void print_factors_full(){
	//char c;
	printf("%llu^%d", factor_val[1], multip[1]);
	for(unsigned int i=2;i<=slotptr;i++) printf(" * %llu^%d", factor_val[i], multip[i]);
	printf("\n");
	return;
}

// Contract: slotptr is the number of the last full slot
bool generate_divisors(unsigned __int128 aim){
	unsigned __int128 ltmp, ltmp1, ltmp2;
	unsigned long int ltmp3;
	ltmp=1;
	for(unsigned int i=1;i<=slotptr;i++){
		ltmp*=multip[i]+1;
	}
	if(ltmp>DIVISOR_BOUND){
		// Error handling: too many divisors
		#ifdef __USING_BOINC
		fio=boinc_fopen("err.txt","ab");
		#else
		fio=fopen("err.txt","ab");
		#endif
		//gmp_printf("%Zd: too many divisors\n", factored[slotptr]);
		gmp_fprintf(fio,"%Zd: too many divisors%c", factored[slotptr], 10);
		fclose(fio);
		return false;
	}
	divisor_cnt=1;
	divisors[0]=1;
	for(unsigned int i=1;i<=slotptr;i++){
		ltmp=divisor_cnt;
		ltmp3=factor_val[i];
		ltmp1=ltmp3;
		for(unsigned int j=0;j<multip[i];j++){
			for(unsigned int k=0;k<ltmp;k++){
				ltmp2=ltmp1*divisors[k];
				if(ltmp2<=aim){
					divisors[divisor_cnt]=ltmp2;
					divisor_cnt++;
				}
			}
			ltmp1*=ltmp3;
		}
	}
	
	// Sort the divisor list
	std::sort(divisors+2, divisors+divisor_cnt);

	// Remove n
	if(divisors[divisor_cnt-1]==mpz_to_u128(factored[slotptr])) divisor_cnt--;

	workpoint+=divisor_cnt;
	wp_res+=divisor_cnt;
	
	return true;
}

bool subset_sum(unsigned long int ptr, unsigned __int128 aim, unsigned __int128 avail){
	if(avail<aim) return false;
	checksum++;
	if(aim<=1) return true;
	unsigned __int128 sss2=avail, sss3;
	unsigned long int myptr=ptr;
	unsigned int cc=0;
	//checksum+=divisors[ptr];
	while(divisors[myptr]>aim){
		sss2-=divisors[myptr];
		myptr--;
		cc++;
	}
	workpoint+=(cc>>2);
	wp_res+=(cc>>2);
	if(sss2<aim) return false;
	if(sss2==aim) return true;
	if(divisors[myptr]==aim) return true;
	if(myptr==0) return false;
	sss3=sss2-aim;
	if(divisors[myptr]==sss3) return true;
	if(sss3>aim){
		if(subset_sum(myptr-1, aim-divisors[myptr], sss2-divisors[myptr])) return true;
		if(subset_sum(myptr-1, aim, sss2-divisors[myptr])) return true;
	}else{
		if(subset_sum(myptr-1, sss3-divisors[myptr], sss2-divisors[myptr])) return true;
		if(subset_sum(myptr-1, sss3, sss2-divisors[myptr])) return true;
	}
	return false;
}

// Contract: slotptr is the number of the last full slot, and we first reach abundance
void check_weird(){
	mpz_sub(gtmp,presum[slotptr],factored[slotptr]);
	mpz_sub(gtmp,gtmp,factored[slotptr]);
	if(mpz_cmp_ui(gtmp,excess_bound)>0){ 
		//gmp_printf("Problem! %Zd\n", factor_bound[slotptr-1].get_mpz_t()); 
		//print_factors_full(); 
		return; 
	}
	p_cnt++;
	
	//print_factors_full();
	mpz_set(gtmp2,gtmp);
	if(!generate_divisors(mpz_to_u128(gtmp))) return;
	//ltmp=mpz_get_ui(gtmp.get_mpz_t());
	unsigned __int128 ltmp2;
	ltmp2=0;
	//gtmp=0;
	for(unsigned int i=0;i<divisor_cnt;i++){ ltmp2+=divisors[i]; }
	if(!subset_sum(divisor_cnt-1,mpz_to_u128(gtmp2),ltmp2)){
		// We found a weird number!
		#ifdef __USING_BOINC
		fio=boinc_fopen("err.txt","ab");
		#else
		fio=fopen("err.txt","ab");
		#endif
		//gmp_printf("%Zd is WEIRD ODD!!!\n", factored[slotptr]);
		gmp_fprintf(fio,"%Zd is WEIRD ODD!!!%c", factored[slotptr], 10);
		//while(1){ltmp1=ltmp1;}
		fclose(fio);
	}
	return;
}

__inline void end_output(){
	FILE* myfile;
	#ifdef __USING_BOINC
	string resolved_name;
	int retval = boinc_resolve_filename_s("result.txt", resolved_name);
	if (retval) {printf("can't resolve filename"); boinc_finish(-1);}
	fio = boinc_fopen(resolved_name.c_str(), "wb");
	#else
	fio=fopen("result.txt","wb");
	#endif
	gmp_fprintf(fio,"%Zd%c", upperbound, 10);
	gmp_fprintf(fio,"%Zd%c", lowerbound, 10);
	fprintf(fio,"%llu%c",excess_bound, 10);
	fprintf(fio, "%u%c", slotptr, 10);
	fprintf(fio, "%llu%c", p_cnt, 10);
	fprintf(fio, "%llu%c", workpoint, 10);
	fprintf(fio, "%llu%c", primepoint, 10);
	fprintf(fio, "%llu%c", checksum, 10);
	fprintf(fio, "%llu%c", sec_num, 10);
	for(unsigned int i=1; i<slotptr; i++) fprintf(fio, "%llu %u %llu%c", factor[i], multip[i], factor_val[i], 10);
	#ifdef __USING_BOINC
	myfile=boinc_fopen("err.txt","r");
	#else
	myfile=fopen("err.txt","r");
	#endif
	if(myfile!=NULL){
		for(int i=0;i<20;i++){
			if(fgets(buffer,4095,myfile)==NULL) break;
			fprintf(fio, "%s%c", buffer, 10);
		}
		fclose(myfile);
	}else{
		if(0==sec_num){
			fprintf(fio, "c%c", 10);
		}else{
			fprintf(fio, "t%c", 10);
		}
	}
	fclose(fio);
	update_progress();
	
	// clean-up for mpz
	for(int i=0;i<129;i++){
		mpz_clears(factored[i],residue[i],presum[i],factor_bound[i],NULL);
	}
	mpz_clears(upperbound,lowerbound,gtmp,gtmp1,gtmp2,gtmp3,gtmp4,gtmp5,ltmp,ltmp1,ltmp2,ltmp3,ltmp4,cnv128tmp,NULL);
	return;
}

void search(unsigned int a){
	// Under certain size assumption of abundance
	// Need to be checked when passing over 128bit
	// OEIS A047802
	// Works for numbers less than 128bit
	if((a==2)&&(factor[1]>3)) return;
	
	if(a>2){
		int tmpslptr=slotptr;
		slotptr=a;
		mpz_pow_ui(gtmp4,factor_bound[slotptr-1],2);
		mpz_mul_ui(gtmp4,gtmp4,SEC_CONST);
		if(mpz_cmp(residue[slotptr-1],gtmp4)<=0){
			mpz_pow_ui(gtmp5,factor_bound[slotptr-2],2);
			mpz_mul_ui(gtmp5,gtmp5,SEC_CONST);
			if(mpz_cmp(residue[slotptr-2],gtmp5)>0){
				sec_num--;
				if(0==sec_num){
					slotptr=tmpslptr;
					end_output();
					#ifdef __USING_BOINC
					boinc_finish(0);
					#else
					exit(0);
					#endif
				}
			}
		}
		if((wp_res>=WORKPOINT_PERIOD)||(pp_res>=PRIMEPOINT_PERIOD)){
			bool wp_flag = (pp_res>=PRIMEPOINT_PERIOD);
			while(wp_res>=WORKPOINT_PERIOD) wp_res-=WORKPOINT_PERIOD;
			while(pp_res>=PRIMEPOINT_PERIOD) pp_res-=PRIMEPOINT_PERIOD;
			if((workpoint>WORKPOINT_LIMIT)||(primepoint>PRIMEPOINT_LIMIT)){
				slotptr=tmpslptr;
				end_output();
				#ifdef __USING_BOINC
				boinc_finish(0);
				#else
				exit(0);
				#endif
			}else{
				slotptr=tmpslptr;
				if(wp_flag) checkpoint();
			}
		}
		slotptr=tmpslptr;
	}
	
	// Reset to checkpoint
	if(a<slotptr){
		search(a+1);
		slotptr--;
	}
	
	// Print progress
	//if(slotptr<=3) print_factors();
	
	unsigned long int myp=factor[slotptr];
	unsigned long int myprime=factor_val[slotptr];
	bool flag=false;
	// Start search
	while(true){
		// Update
		if(myp==0){
			// We newly arrive.
			myp=factor[slotptr-1]+1;
			myprime=next_factor[slotptr-1];
			if(mpz_cmp_ui(factor_bound[slotptr-1],myprime)>0){
				myprime=getnextprime2(&myp, mpz_get_ui(factor_bound[slotptr-1]));
				// check for formula barrier
				mpz_tdiv_q_ui(ltmp,residue[slotptr-1],myprime);
				mpz_set_ui(ltmp1,myprime);
				mpz_set_ui(ltmp2,myprime-1);
				while(mpz_cmp(ltmp1,ltmp)<=0){ 
					mpz_mul_ui(ltmp1,ltmp1,myprime); 
					mpz_mul_ui(ltmp2,ltmp2,myprime-1); 
				}
				mpz_mul_2exp(gtmp,factored[slotptr-1],1);
				mpz_mul(gtmp,gtmp,ltmp2);
				mpz_mul(gtmp2,presum[slotptr-1],ltmp1);
				if(mpz_cmp(gtmp2,gtmp)<=0){
					factor[slotptr]=0;
					multip[slotptr]=0;
					factor_val[slotptr]=0;
					next_factor[slotptr]=0;
					mpz_set_ui(factor_bound[slotptr],0);
					return;
				}
			}
			if(mpz_cmp_ui(residue[slotptr-1],myprime)<0){
				// Range exceeded if we add this factor
				return;
			}
			factor[slotptr]=myp;
			multip[slotptr]=1;
			factor_val[slotptr]=myprime;
			next_factor[slotptr]=getnextprime(factor[slotptr],factor_val[slotptr]);
			mpz_mul_ui(factored[slotptr],factored[slotptr-1],myprime);
			mpz_mul_ui(presum[slotptr],presum[slotptr-1],(1+myprime));
			/*
			residue[slotptr]=residue[slotptr-1]/myprime;
			gtmp4=factored[slotptr];
			gtmp4+=factored[slotptr];
			gtmp5=gtmp4;
			gtmp5-=presum[slotptr];
			gtmp4-=excess_bound+1;
			gtmp4/=gtmp5;
			factor_bound[slotptr]=gtmp4;
			*/
		}else{
			// We were already here.
			if((mpz_cmp_ui(residue[slotptr],myprime)>=0)&&(!flag)){ 
				// We can still add a factor
				multip[slotptr]++;
				mpz_mul_ui(factored[slotptr],factored[slotptr],myprime);
				mpz_mul_ui(presum[slotptr],presum[slotptr],myprime);
				mpz_add(presum[slotptr],presum[slotptr],presum[slotptr-1]);
				/*
				residue[slotptr]/=myprime;
				gtmp4=factored[slotptr];
				gtmp4+=factored[slotptr];
				gtmp5=gtmp4;
				gtmp5-=presum[slotptr];
				gtmp4-=excess_bound+1;
				gtmp4/=gtmp5;
				factor_bound[slotptr]=gtmp4;
				*/
			}else{ 
				// We should change factor, and probably check for formula barrier
				flag=false;
				myp++;
				myprime=next_factor[slotptr];
				//gmp_printf("%d >= %Zd\n", myprime, factor_bound[slotptr-1].get_mpz_t());
				if(mpz_cmp_ui(residue[slotptr-1],myprime)<0){ // Range exceeded if we add this factor
					factor[slotptr]=0;
					multip[slotptr]=0;
					factor_val[slotptr]=0;
					next_factor[slotptr]=0;
					mpz_set_ui(factor_bound[slotptr],0);
					return;
				}
				// Check for formula barrier
				if((myp&15)==0){
					mpz_tdiv_q_ui(ltmp,residue[slotptr-1],myprime);
					mpz_set_ui(ltmp1,myprime);
					mpz_set_ui(ltmp2,myprime-1);
					while(mpz_cmp(ltmp1,ltmp)<=0){ 
						mpz_mul_ui(ltmp1,ltmp1,myprime); 
						mpz_mul_ui(ltmp2,ltmp2,myprime-1); 
					}
					mpz_mul_2exp(gtmp,factored[slotptr-1],1);
					mpz_mul(gtmp,gtmp,ltmp2);
					mpz_mul(gtmp2,presum[slotptr-1],ltmp1);
					if(mpz_cmp(gtmp2,gtmp)<=0){
						factor[slotptr]=0;
						multip[slotptr]=0;
						factor_val[slotptr]=0;
						next_factor[slotptr]=0;
						mpz_set_ui(factor_bound[slotptr],0);
						return;
					}
				}
				// Change factor
				factor[slotptr]=myp;
				multip[slotptr]=1;
				factor_val[slotptr]=myprime;
				next_factor[slotptr]=getnextprime(factor[slotptr],factor_val[slotptr]);
				mpz_mul_ui(factored[slotptr],factored[slotptr-1],myprime);
				mpz_mul_ui(presum[slotptr],presum[slotptr-1],(myprime+1));
				/*
				residue[slotptr]=residue[slotptr-1]/myprime;
				gtmp4=factored[slotptr];
				gtmp4+=factored[slotptr];
				gtmp5=gtmp4;
				gtmp5-=presum[slotptr];
				gtmp4-=excess_bound+1;
				gtmp4/=gtmp5;
				factor_bound[slotptr]=gtmp4;
				*/
			}
		}
		
		// Check
		mpz_mul_2exp(gtmp,factored[slotptr],1);
		if(mpz_cmp(gtmp,presum[slotptr])<=0){ // We reach a tail-primitive abundant number
			
			if(mpz_cmp(factored[slotptr],lowerbound)>0){
				check_weird();
			}
			
			if((wp_res>=WORKPOINT_PERIOD)||(pp_res>=PRIMEPOINT_PERIOD)){
				bool wp_flag=(pp_res>=PRIMEPOINT_PERIOD);
				while(wp_res>=WORKPOINT_PERIOD) wp_res-=WORKPOINT_PERIOD;
				while(pp_res>=PRIMEPOINT_PERIOD) pp_res-=PRIMEPOINT_PERIOD;
				if((workpoint>WORKPOINT_LIMIT)||(primepoint>PRIMEPOINT_LIMIT)){
					end_output();
					#ifdef __USING_BOINC
					boinc_finish(0);
					#else
					exit(0);
					#endif
				}else if(wp_flag){
					slotptr++;
					checkpoint();
					slotptr--;
				}
			}
			
			// Still it is abundant and we are not going further.
			flag=true;
		}
		
		if(!flag){
			if(multip[slotptr]==1){
				mpz_tdiv_q_ui(residue[slotptr],residue[slotptr-1],myprime);
			}else{
				mpz_tdiv_q_ui(residue[slotptr],residue[slotptr],myprime);
			}
			// Spring-off
			if(mpz_cmp_ui(residue[slotptr],next_factor[slotptr])>=0){
				mpz_mul_2exp(gtmp4,factored[slotptr],1);
				mpz_sub(gtmp5,gtmp4,presum[slotptr]);
				mpz_sub_ui(gtmp4,gtmp4,excess_bound+1);
				mpz_tdiv_q(gtmp4,gtmp4,gtmp5);
				mpz_set(factor_bound[slotptr],gtmp4);
				next_factor[slotptr]--;
				if(mpz_cmp_ui(factor_bound[slotptr],next_factor[slotptr])<0){
					mpz_set_ui(factor_bound[slotptr],next_factor[slotptr]);
				}
				next_factor[slotptr]++;
				if(mpz_cmp(residue[slotptr],factor_bound[slotptr])>=0){
					slotptr++;
					search(a+1);
					slotptr--;
				}
			}
		}
	}
	
	return;
}

int main(){
	#ifdef __USING_BOINC
	boinc_init();
	#endif
	init();
	search(1);
	end_output();
	#ifdef __USING_BOINC
	boinc_finish(0);
	#else
	exit(0);
	#endif
}
