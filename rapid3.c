#include "arb_mat.h"
#include "arb_hypgeom.h"
#include "acb_hypgeom.h"
#include "acb_dirichlet.h"
#include "flint/profiler.h"

#define VERBOSE 1

static double
log_gamma_upper_approx(double a, double z)
{
    if (a < z)
        return (a - 1) * log(z) - z;
    else
        return a * (log(a) - 1);
}

void
acb_dirichlet_root_number2(acb_t res, const dirichlet_group_t G, const dirichlet_char_t chi, slong prec)
{
    acb_dirichlet_root_number(res, G, chi, prec);

    if (dirichlet_char_is_real(G, chi))
        arb_zero(acb_imagref(res));
}


/* todo: input abs_tol accounts for 1/n^s ? */

/* error is bounded by first neglected term if N >= a - 1 */
static slong
gamma_upper_N_upper(mag_t err, const fmpq_t a, const arb_t z, const mag_t abs_tol)
{
    slong N, aa, ab;
    fmpz_t az1, az2;
    mag_t t, u;

#if 0
    printf("choose asympt for a = "); fmpq_print(a); printf("  z = "); arb_printd(z, 5); printf("abs_tol = "); mag_printd(abs_tol, 5); printf("\n");
#endif

    fmpz_init(az1);
    fmpz_init(az2);
    mag_init(t);
    mag_init(u);

    fmpz_fdiv_q(az1, fmpq_numref(a), fmpq_denref(a));
    fmpz_cdiv_q(az2, fmpq_numref(a), fmpq_denref(a));

    if (!fmpz_fits_si(az1) || !fmpz_fits_si(az2))
    {
        mag_inf(err);
        N = -1;
    }
    else
    {
        aa = fmpz_get_si(az1);
        ab = fmpz_get_si(az2);

        /* prefactor z^(a-1) * exp(-z) */
        arb_get_mag_lower(t, z);
        mag_expinv(t, t);

        arb_get_mag(u, z);
        if (ab >= 1)
        {
            mag_pow_ui(u, u, ab - 1);
        }
        else
        {
            mag_pow_ui_lower(u, u, 1 - ab);
            mag_inv(u, u);
        }
        mag_mul(err, t, u);

        arb_get_mag_lower(t, z);
        mag_inv(t, t);

//        printf("prefactor: "); mag_printd(err, 5); printf("  1/z  "); mag_printd(t, 5); printf("\n");

        for (N = 1; ; N++)
        {
            mag_mul_ui(u, err, FLINT_MAX(FLINT_ABS(aa - N), FLINT_ABS(ab - N)));
            mag_mul(u, u, t);

//            printf("N = %ld ", N); mag_printd(u, 5); printf("\n");

            if (N >= ab - 1 && mag_cmp(u, abs_tol) < 0)
            {
                mag_swap(err, u);
                break;
            }

            /* Stop if terms are increasing, unless a is a positive integer in
               which case the series will terminate eventually. */
            if (mag_cmp(u, err) > 0 && !(aa == ab && aa >= 1))
            {
                mag_inf(err);
                N = -1;
                break;
            }

            mag_swap(err, u);
        }
    }

    fmpz_clear(az1);
    fmpz_clear(az2);
    mag_clear(t);
    mag_clear(u);

    return N;
}

static void
upper_bsplit(arb_t M, arb_t S, arb_t Q, const fmpz_t ap, const fmpz_t aq, const arb_t z, slong na, slong nb, int cont, slong prec)
{
    if (nb == na) flint_abort();

    if (nb - na == 1)
    {
        fmpz_t t;
        fmpz_init_set(t, ap);
        fmpz_submul_ui(t, aq, na + 1);
        fmpz_neg(t, t);
        arb_set_fmpz(M, t);
        arb_mul_fmpz(S, z, aq, prec);
        arb_neg(S, S);
        arb_set(Q, S);
        fmpz_clear(t);
    }
    else
    {
        slong m;
        arb_t M2, S2, Q2;

        m = na + (nb - na) / 2;

        arb_init(M2);
        arb_init(S2);
        arb_init(Q2);

        upper_bsplit(M, S, Q, ap, aq, z, na, m, 1, prec);
        upper_bsplit(M2, S2, Q2, ap, aq, z, m, nb, cont, prec);

        /* todo: squaring opt; power table */
        arb_mul(S, S, Q2, prec);
        arb_addmul(S, M, S2, prec);

        if (cont)
            arb_mul(M, M, M2, prec);

        arb_mul(Q, Q, Q2, prec);

        arb_clear(M2);
        arb_clear(S2);
        arb_clear(Q2);
    }
}

static void
gamma_upper_asymp(arb_t res, const fmpq_t a, const arb_t z, slong N, slong prec)
{
    arb_t M, S, Q;
    fmpq_t a1;

    arb_init(M);
    arb_init(S);
    arb_init(Q);
    fmpq_init(a1);

    upper_bsplit(M, S, Q, fmpq_numref(a), fmpq_denref(a), z, 0, N, 0, prec);
    arb_div(S, S, Q, prec);

    fmpq_sub_ui(a1, a, 1);
    arb_pow_fmpq(M, z, a1, prec);
    arb_mul(S, S, M, prec);

    arb_neg(M, z);
    arb_exp(M, M, prec);
    arb_mul(res, S, M, prec);

    arb_clear(M);
    arb_clear(S);
    arb_clear(Q);
    fmpq_clear(a1);
}

/* select N and bound error for z**a * exp(-z) / a * sum(z**n / rf(a+1, n)) */

static void
mag_div_fmpq(mag_t res, const mag_t x, const fmpq_t a)
{
    mag_t t;
    mag_init(t);
    mag_set_fmpz_lower(t, fmpq_numref(a));
    mag_div(res, x, t);
    mag_set_fmpz(t, fmpq_denref(a));
    mag_mul(res, res, t);
    mag_clear(t);
}

static slong
gamma_lower_N(mag_t err, const fmpq_t a, const arb_t z, const mag_t abs_tol)
{
    slong N, aa, ab, c;
    fmpz_t az1, az2;
    mag_t t, u;

    fmpz_init(az1);
    fmpz_init(az2);
    mag_init(t);
    mag_init(u);

    fmpz_fdiv_q(az1, fmpq_numref(a), fmpq_denref(a));
    fmpz_cdiv_q(az2, fmpq_numref(a), fmpq_denref(a));

    if (!fmpz_fits_si(az1) || !fmpz_fits_si(az2))
    {
        mag_inf(err);
        N = -1;
    }
    else
    {
        aa = fmpz_get_si(az1);
        ab = fmpz_get_si(az2);

        /* prefactor z^a * exp(-z) / a */
        arb_get_mag_lower(t, z);
        mag_expinv(t, t);

        arb_get_mag(u, z);
        if (ab >= 0)
        {
            mag_pow_ui(u, u, ab);
        }
        else
        {
            mag_pow_ui_lower(u, u, -ab);
            mag_inv(u, u);
        }
        mag_mul(err, t, u);
        mag_div_fmpq(err, err, a);

        arb_get_mag(t, z);

//        printf("prefactor: "); mag_printd(err, 5); printf("  1/z  "); mag_printd(t, 5); printf("\n");

        for (N = 1; ; N++)
        {
            c = FLINT_MIN(FLINT_ABS(aa + N), FLINT_ABS(ab + N));

//            printf("%ld: ", N); mag_printd(err, 5); printf(" "); mag_printd(abs_tol, 5); printf("\n");

            if (c == 0)
            {
                fmpq_t q;
                fmpq_init(q);
                fmpq_add_ui(q, q, N);
                mag_div_fmpq(err, err, q);
                fmpq_clear(q);
            }
            else
            {
                mag_div_ui(err, err, c);
            }

            mag_mul(err, err, t);

            /* todo: condition can be relaxed */
            /* todo: faster check (compare t) */
            if ((aa + N) > 0 && mag_cmp(err, abs_tol) < 0)
            {
                mag_div_ui(u, t, aa + N);
                mag_geom_series(u, u, 0);
                mag_mul(u, err, u);

                if (mag_cmp(u, abs_tol) < 0)
                {
                    mag_swap(err, u);
                    break;
                }
            }
        }
    }

    fmpz_clear(az1);
    fmpz_clear(az2);
    mag_clear(t);
    mag_clear(u);

    return N;
}

/* z*aq, ap+aq*(na+1), ap+aq*(na+1) */
static void
lower_bsplit(arb_t M, arb_t S, arb_t Q, const fmpz_t ap, const fmpz_t aq, const arb_t z, slong na, slong nb, int cont, slong prec)
{
    if (nb == na) flint_abort();

    if (nb - na == 1)
    {
        fmpz_t t;
        fmpz_init_set(t, ap);
        fmpz_addmul_ui(t, aq, na + 1);
        arb_set_fmpz(S, t);
        arb_set(Q, S);
        arb_mul_fmpz(M, z, aq, prec);
        fmpz_clear(t);
    }
    else
    {
        slong m;
        arb_t M2, S2, Q2;

        m = na + (nb - na) / 2;

        arb_init(M2);
        arb_init(S2);
        arb_init(Q2);

        lower_bsplit(M, S, Q, ap, aq, z, na, m, 1, prec);
        lower_bsplit(M2, S2, Q2, ap, aq, z, m, nb, cont, prec);

        /* todo: squaring opt; power table */

        /* todo: exploit S2 = Q2 ... */
        arb_mul(S, S, Q2, prec);
        arb_addmul(S, M, S2, prec);

        if (cont)
            arb_mul(M, M, M2, prec);

        arb_mul(Q, Q, Q2, prec);

        arb_clear(M2);
        arb_clear(S2);
        arb_clear(Q2);
    }
}

static void
gamma_lower(arb_t res, const fmpq_t a, const arb_t z, slong N, slong prec)
{
    arb_t M, S, Q;

    arb_init(M);
    arb_init(S);
    arb_init(Q);

    lower_bsplit(M, S, Q, fmpq_numref(a), fmpq_denref(a), z, 0, N, 0, prec);
    arb_div(S, S, Q, prec);

    arb_pow_fmpq(M, z, a, prec);
    arb_mul(S, S, M, prec);

    arb_neg(M, z);
    arb_exp(M, M, prec);
    arb_mul(S, S, M, prec);

    arb_div_fmpz(S, S, fmpq_numref(a), prec);
    arb_mul_fmpz(res, S, fmpq_denref(a), prec);

    arb_clear(M);
    arb_clear(S);
    arb_clear(Q);
}

static void
taylor_M(mag_t M, const arb_t a, const arb_t z, const mag_t x, slong Rexp)
{
    arb_t t, u;
    arb_init(t);
    arb_init(u);

    arb_sub_ui(u, a, 1, 53);
    arb_sgn(t, u);
    arb_mul_2exp_si(t, t, Rexp);
    arb_add(t, z, t, 53);
    arb_pow(t, t, u, 53);

    arb_one(u);
    arb_mul_2exp_si(u, u, Rexp);
    arb_sub(u, u, z, 53);
    arb_exp(u, u, 53);

    arb_mul(t, t, u, 53);

    arb_get_mag(M, t);

    arb_clear(t);
    arb_clear(u);
}

/* choose N such that M * C^N / (1 - C) <= tol */
/* todo: fix */
static slong
mag_geom_choose_N(const mag_t M, const mag_t C, const mag_t tol)
{
    mag_t t, u;
    slong N;

    /* N = log(M / ((1 - C) tol)) / log(1/C) */
    mag_init(t);
    mag_init(u);

    mag_one(t);
    mag_sub_lower(t, t, C);
    mag_mul_lower(t, t, tol);
    mag_div(t, M, t);
    mag_log(t, t);

    mag_inv_lower(u, C);
    mag_log_lower(u, u);
    mag_div(t, t, u);

    N = ceil(mag_get_d(t));
    N = FLINT_MAX(N, 1);

    mag_clear(t);
    mag_clear(u);

    return N;
}

static void
taylor_bound(mag_t err, const arb_t a, const arb_t z, const mag_t x, slong Rexp, slong N)
{
    mag_t C, M;

    mag_init(C);
    mag_init(M);

    /* C = x / R */
    mag_mul_2exp_si(C, x, -Rexp);

    /* M R C^n / (1 - C) / N */
    mag_geom_series(err, C, N);

    if (!mag_is_inf(err))
    {
        taylor_M(M, a, z, x, Rexp);
        mag_mul(err, err, M);

        mag_mul_2exp_si(err, err, Rexp);
        mag_div_ui(err, err, N);
    }

    mag_clear(C);
    mag_clear(M);
}

static slong
taylor_N(const arb_t a, const arb_t z, const mag_t x, slong Rexp, const mag_t abs_tol)
{
    mag_t C, M;
    slong N;

    mag_init(C);
    mag_init(M);

    /* C = x / R */
    mag_mul_2exp_si(C, x, -Rexp);

    if (mag_cmp_2exp_si(C, 0) < 0)
    {
        taylor_M(M, a, z, x, Rexp);
        mag_mul_2exp_si(M, M, Rexp);

        N = mag_geom_choose_N(M, C, abs_tol);
    }
    else
    {
        N = WORD_MAX;
    }


    mag_clear(C);
    mag_clear(M);

    return N;
}

static void
arb_hypgeom_gamma_upper_taylor_choose(slong * res_N, mag_t err, const arb_t a, const arb_t z, const mag_t x, const mag_t abs_tol)
{
    slong N, New;
    mag_t zlow;
    slong Rexp;

    mag_init(zlow);
    arb_get_mag_lower(zlow, z);

    Rexp = 0;
    while (mag_cmp_2exp_si(zlow, Rexp + 1) < 0)
        Rexp--;

#if VERBOSE
//    printf("initial Rexp %ld; z = %f\n", Rexp, mag_get_d(zlow));
#endif

    N = taylor_N(a, z, x, Rexp, abs_tol);

#if 1

    while (N > 1 && mag_cmp_2exp_si(x, Rexp - 1) < 0)
    {
        New = taylor_N(a, z, x, Rexp - 1, abs_tol);

        if (New <= N)
        {
            Rexp = Rexp - 1;
            N = New;
        }
        else
        {
            break;
        }
    }

    if (Rexp == 0)
    {
        while (N > 1 && mag_cmp_2exp_si(zlow, Rexp + 1) > 0)
        {
            New = taylor_N(a, z, x, Rexp + 1, abs_tol);

            if (New <= N)
            {
                Rexp = Rexp + 1;
                N = New;
            }
            else
            {
                break;
            }
        }
    }

#endif

    *res_N = N;
    taylor_bound(err, a, z, x, Rexp, N);

    if (mag_cmp(err, abs_tol) > 0)
    {
        printf("err = "); mag_printd(err, 10); printf("\n");
        printf("abs_tol = "); mag_printd(abs_tol, 10); printf("\n");
        printf("a = "); arb_printd(a, 10); printf("\n");
        printf("z = "); arb_printd(z, 10); printf("\n");
        printf("x = "); mag_printd(x, 10); printf("\n");
        printf("Rexp = "); printf("%ld\n", Rexp); printf("\n");
        printf("N = "); printf("%ld\n", N); printf("\n");
        flint_abort();
    }

    mag_clear(zlow);
}

static void
gamma_upper_taylor_bsplit(arb_mat_t M, arb_t Q, const fmpz_t ap, const fmpz_t aq, const arb_t z0, const arb_t x, const arb_t x2, slong a, slong b, int cont, slong prec)
{
    if (b - a == 0)
    {
        arb_mat_one(M);
    }
    else if (b - a == 1)   /* todo: inline b - a == 2 ? */
    {
        slong n;
        fmpz_t t;

        n = a;
        fmpz_init(t);

        /* Q = -z0*(n+1)*(n+2)*aq */
        fmpz_mul2_uiui(t, aq, n + 1, n + 2);
        arb_mul_fmpz(Q, z0, t, prec);
        arb_neg(Q, Q);

        /* x Q */
        arb_mul(arb_mat_entry(M, 0, 1), Q, x, prec);

        /* aq n x */
        fmpz_mul_ui(t, aq, n);
        arb_mul_fmpz(arb_mat_entry(M, 1, 0), x, t, prec);

// x*(n+1)*(aq(n+1+z)-ap)

        /* x*(-ap + aq*(n + z0 + 1))*(n + 1) */
        arb_add_ui(arb_mat_entry(M, 1, 1), z0, n + 1, prec);
        arb_mul_fmpz(arb_mat_entry(M, 1, 1), arb_mat_entry(M, 1, 1), aq, prec);
        arb_sub_fmpz(arb_mat_entry(M, 1, 1), arb_mat_entry(M, 1, 1), ap, prec);
        arb_mul_ui(arb_mat_entry(M, 1, 1), arb_mat_entry(M, 1, 1), n + 1, prec);
        arb_mul(arb_mat_entry(M, 1, 1), arb_mat_entry(M, 1, 1), x, prec);

        arb_set(arb_mat_entry(M, 2, 0), Q);
        arb_set(arb_mat_entry(M, 2, 2), Q);

        fmpz_clear(t);
    }
/*
    else if (0 && b - a <= 8)
    {
        arb_mat_t M1, M2;
        arb_t Q2;
        slong m;

        arb_mat_init(M1, 3, 3);
        arb_mat_init(M2, 3, 3);
        arb_init(Q2);

        gamma_upper_taylor_bsplit(M, Q, ap, aq, z0, x, x2, a, a + 1, prec);

        for (m = a + 1; m < b; m++)
        {
            gamma_upper_taylor_bsplit(M2, Q2, ap, aq, z0, x, x2, m, m + 1, prec);
            arb_mat_mul(M1, M2, M, prec);
            arb_mat_swap(M, M1);
            arb_mul(Q, Q2, Q, prec);
        }

        arb_mat_clear(M1);
        arb_mat_clear(M2);
        arb_clear(Q2);
    }
*/
    else
    {
        arb_mat_t M1, M2;
        arb_t Q2;
        slong m;

        arb_mat_init(M1, 3, 3);
        arb_mat_init(M2, 3, 3);
        arb_init(Q2);

        m = a + (b - a) / 2;

        gamma_upper_taylor_bsplit(M1, Q, ap, aq, z0, x, x2, a, m, 1, prec);
        gamma_upper_taylor_bsplit(M2, Q2, ap, aq, z0, x, x2, m, b, cont, prec);

        if (cont)
        {
            arb_mat_mul(M, M2, M1, prec);
        }
        else
        {
            arb_mat_transpose(M1, M1);

            arb_dot(arb_mat_entry(M, 2, 0), NULL, 0, arb_mat_entry(M1, 0, 0), 1, arb_mat_entry(M2, 2, 0), 1, 3, prec);
            arb_dot(arb_mat_entry(M, 2, 1), NULL, 0, arb_mat_entry(M1, 1, 0), 1, arb_mat_entry(M2, 2, 0), 1, 3, prec);
            arb_dot(arb_mat_entry(M, 2, 2), NULL, 0, arb_mat_entry(M1, 2, 0), 1, arb_mat_entry(M2, 2, 0), 1, 3, prec);
        }

        arb_mul(Q, Q2, Q, prec);

        arb_mat_clear(M1);
        arb_mat_clear(M2);
        arb_clear(Q2);
    }
}

static void
_arf_trunc(arf_t x)
{
    if (arf_sgn(x) < 0)
        arf_ceil(x, x);
    else
        arf_floor(x, x);
}

static void
arb_extract_bits(arb_t t, const arb_t z, slong b)
{
    arb_mul_2exp_si(t, z, b);
    _arf_trunc(arb_midref(t));
    mag_zero(arb_radref(t));
    arb_mul_2exp_si(t, t, -b);
}

static void
acb_dirichlet_afe_tail_bound(mag_t res, const fmpq_t sd2, slong N, ulong q, int parity)
{
    mag_t pi_n2_q, t, u;
    fmpz_t sprime;

    mag_init(pi_n2_q);
    mag_init(t);
    mag_init(u);
    fmpz_init(sprime);

    /* pi_n2_q = pi * N^2 / q (lower bound) */
    mag_const_pi_lower(pi_n2_q);
    mag_mul_ui_lower(pi_n2_q, pi_n2_q, N);
    mag_mul_ui_lower(pi_n2_q, pi_n2_q, N);
    mag_set_ui(t, q);
    mag_div_lower(pi_n2_q, pi_n2_q, t);

    /* upper bound for sd2 */
    fmpz_cdiv_q(sprime, fmpq_numref(sd2), fmpq_denref(sd2));

    /* require pi_n2_q > s' */
    mag_set_fmpz(t, sprime);
    if (fmpz_sgn(sprime) > 0 && mag_cmp(pi_n2_q, t) <= 0)
    {
        mag_inf(res);
    }
    else
    {
        mag_expinv(res, pi_n2_q);

        mag_div_ui(res, res, N);
        if (!parity)
            mag_div_ui(res, res, N);

        /* (1 + q/pi) */
        mag_set_ui(t, q);
        mag_const_pi_lower(u);
        mag_div(t, t, u);
        mag_add_ui(t, t, 1);
        mag_mul(res, res, t);

        /* max(1, 2^s') */
        if (fmpz_sgn(sprime) > 0)
            mag_mul_2exp_fmpz(res, res, sprime);

        /* (pi/q)^(s'-1) */
        fmpz_sub_ui(sprime, sprime, 1);
        if (fmpz_sgn(sprime) >= 0)
        {
            mag_const_pi(t);
            mag_set_ui_lower(u, q);
            mag_div(t, t, u);
            mag_pow_fmpz(t, t, sprime);
        }
        else
        {
            mag_const_pi_lower(t);
            mag_set_ui(u, q);
            mag_div_lower(t, t, u);

            fmpz_neg(sprime, sprime);
            mag_pow_fmpz_lower(t, t, sprime);
            mag_inv(t, t);
        }

        mag_mul(res, res, t);
    }

    mag_clear(pi_n2_q);
    mag_clear(t);
    mag_clear(u);
    fmpz_clear(sprime);
}

/* 
Given Gz0 = Gamma(a, z0) and expmz0 = exp(-z0), compute Gz1 = Gamma(a, z1)
*/
void
arb_gamma_upper_fmpq_continuation(arb_t Gz1, const fmpq_t a, const arb_t z0, const arb_t z1, const arb_t Gz0, const arb_t expmz0, const mag_t abs_tol, slong prec)
{
    arb_t x, x2, Q, a_real;
    arb_mat_t M;
    mag_t xmag, err;
    slong N;
    fmpq_t a1;

    mag_init(xmag);
    mag_init(err);
    arb_init(x);
    arb_init(x2);
    arb_init(Q);
    arb_init(a_real);
    fmpq_init(a1);
    arb_mat_init(M, 3, 3);

    arb_sub(x, z1, z0, prec);
    arb_get_mag(xmag, x);
//    arb_mul(x2, x, x, prec);

#if VERBOSE
//    printf("TRY CONTINUATION  a = %f, z0 = %f\n", fmpq_get_d(a), arf_get_d(arb_midref(z0), ARF_RND_NEAR));
#endif

    arb_set_fmpq(a_real, a, 53);
    arb_hypgeom_gamma_upper_taylor_choose(&N, err, a_real, z0, xmag, abs_tol);

 //   printf("abs_tol = "); mag_printd(abs_tol, 10); printf("\n");
//    printf("err     = "); mag_printd(err, 10); printf("\n");

//    N = 2;

    gamma_upper_taylor_bsplit(M, Q, fmpq_numref(a), fmpq_denref(a), z0, x, NULL, 0, N, 0, prec);

/*
    printf("N = %ld\n", N);
    fmpq_print(a); printf("\n");
    arb_printd(z0, 30); printf("\n");
    arb_printd(x, 30); printf("\n");
    arb_mat_printd(M, 30); printf("\n");
    arb_printd(Q, 30); printf("\n");

    flint_abort();
*/

    /* S = (M[2,0] + Gz0*M[2,2] + x*(-z0**(a-1) * exp(-z0))*M[2,1]) / Q */


    /* S = (Gz0*M[2,0] + (-z0**(a-1) * exp(-z0))*M[2,1]) / Q */

    arb_mul(arb_mat_entry(M, 2, 0), arb_mat_entry(M, 2, 0), Gz0, prec);

    fmpq_sub_ui(a1, a, 1);
    arb_pow_fmpq(arb_mat_entry(M, 0, 0), z0, a1, prec);
    arb_mul(arb_mat_entry(M, 0, 0), arb_mat_entry(M, 0, 0), expmz0, prec);
    arb_submul(arb_mat_entry(M, 2, 0), arb_mat_entry(M, 2, 1), arb_mat_entry(M, 0, 0), prec);

    arb_div(Gz1, arb_mat_entry(M, 2, 0), Q, prec);

    arb_add_error_mag(Gz1, err);

    mag_clear(xmag);
    mag_clear(err);
    arb_clear(x);
    arb_clear(x2);
    arb_clear(Q);
    arb_clear(a_real);
    fmpq_clear(a1);
    arb_mat_clear(M);
}

void
acb_dirichlet_fmpq_sum_afe(acb_t res, const fmpq_t s, const dirichlet_group_t G, const dirichlet_char_t chi, const mag_t abs_tol, slong prec)
{
    slong n, start_bits, bits, wp, wp2, wp3, gamma_cached_prec;
    mag_t err, abs_tol_gamma;
    arb_t s_real, ns, t, u, v, z, z0, z1, x, x2, Ga, Gz1, Gz0, expmz0, z0_prevn, Gz0_prevn, expmz0_prevn;
    acb_t c;
    fmpq_t s2;
    int parity;
    ulong q;

    mag_init(err);
    mag_init(abs_tol_gamma);
    arb_init(s_real);
    arb_init(ns);
    arb_init(t);
    arb_init(u);
    arb_init(v);
    arb_init(z);
    arb_init(z0);
    arb_init(z1);
    arb_init(x);
    arb_init(x2);
    arb_init(Ga);
    arb_init(Gz0);
    arb_init(Gz1);
    arb_init(expmz0);
    arb_init(z0_prevn);
    arb_init(Gz0_prevn);
    arb_init(expmz0_prevn);
    acb_init(c);
    fmpq_init(s2);

    if (G == NULL)
    {
        parity = 0;
        q = 1;
    }
    else
    {
        parity = dirichlet_parity_char(G, chi);
        q = G->q;
    }

    arb_set_fmpq(s_real, s, prec);

    acb_zero(res);

    gamma_cached_prec = prec * 1.05 + 30;

    /* todo avoid recompute s2 below */
    fmpq_add_ui(s2, s, parity);
    fmpq_div_2exp(s2, s2, 1);
    arb_gamma_fmpq(Ga, s2, gamma_cached_prec);

    double t1, t2, t3;

    for (n = 1; ; n += 1)
    {
#if VERBOSE
        printf("-----------------------------------------------------------\n");
        flint_printf("n = %wd   (s+parity)/2 = %f  z = %f   q = %wu\n", n, fmpq_get_d(s2), 3.1415926535897932 * n * n / q, q);
#endif

        acb_dirichlet_afe_tail_bound(err, s2, n, q, parity);

#if VERBOSE
        printf("  abs_tol = "); mag_printd(abs_tol, 5); printf("\n");
        printf("  truncation error = "); mag_printd(err, 5); printf("\n");
#endif

        if (mag_cmp(err, abs_tol) < 0)
        {
            if (G == NULL || dirichlet_char_is_real(G, chi))
                arb_add_error_mag(acb_realref(res), err);
            else
                acb_add_error_mag(res, err);

            break;
        }

        double abs_tol_mag;
        double gammainc_mag, gamma_mag, ns_mag;
        double aa, zz;
        double cancellation;

        abs_tol_mag = mag_get_d_log2_approx(abs_tol);

        aa = fmpq_get_d(s2);
        zz = 3.1415926535897932385 * n * n / q;

        /* Gamma((s+parity)/2, z)  (want lower bound, to estimate cancellation) */
        gammainc_mag = log_gamma_upper_approx(aa, zz) / log(2);

        /* Gamma((s+parity)/2) */
        gamma_mag = ARF_EXP(arb_midref(Ga));

        /* n^-s */
        ns_mag = -fmpq_get_d(s) * log(n) / log(2);

        cancellation = FLINT_MAX(gamma_mag - gammainc_mag, 0);

        /* Want Gamma(a,z) n^-s with abs_tol --> want Gamma(a,z) with abs_tol * n^s */
        mag_set_ui_2exp_si(abs_tol_gamma, 1, abs_tol_mag - ns_mag);

        /* Precision needed sans cancellation. */
        wp = gammainc_mag + ns_mag - abs_tol_mag + 5;
        wp = FLINT_MAX(wp, 30);

        /* Precision needed with cancellation. */
        wp2 = FLINT_MAX(gamma_mag, gammainc_mag) + ns_mag - abs_tol_mag + 5;
        wp2 = FLINT_MAX(wp2, 30);


#if VERBOSE
        printf("  abs_tol_gamma = "); mag_printd(abs_tol_gamma, 5); printf("\n");
        printf("  gamma(a)      = "); arb_printd(Ga, 10); printf("\n");
#endif


#if VERBOSE
        printf("  cancellation = %f\n", cancellation);
        printf("  wp = %ld   wp2 = %ld\n", wp, wp2);
#endif

/*
        slong lower_wp;
        slong asymp_wp;
        wp2 = prec - (4.53236014182719 * n * n) / q + 5;
        wp2 = FLINT_MAX(wp2, 48);
        wp2 = prec;
        wp = prec;
*/

        if (G == NULL)
            acb_one(c);
        else
            acb_dirichlet_chi(c, G, chi, n, wp);

        if (acb_is_zero(c))
            continue;

        arb_const_pi(z, wp2);
        arb_mul_ui(z, z, n, wp2);
        arb_mul_ui(z, z, n, wp2);
        arb_div_ui(z, z, q, wp2);

        start_bits = 32;

        arb_extract_bits(z0, z, start_bits);

        //arb_set_fmpq(t, s2, wp2);  // kill???
        //arb_indeterminate(t);

        slong NN;
        mag_t AE;
        mag_init(AE);
        NN = gamma_upper_N_upper(AE, s2, z0, abs_tol_gamma);

        t1 = clock();

        if (n < 60 || 1)
        {
            if (NN != -1)
            {
                gamma_upper_asymp(Gz0, s2, z0, NN, wp);
                arb_add_error_mag(Gz0, AE);
#if VERBOSE
                flint_printf("  asymptotic series with N = %wd: ", NN); arb_printd(Gz0, 10); printf("\n");
#endif
            }
            else
            {
                NN = gamma_lower_N(AE, s2, z0, abs_tol_gamma);
                gamma_lower(Gz0, s2, z0, NN, wp2);
                arb_add_error_mag(Gz0, AE);
//                printf("G:        "); arb_printd(G, 10); printf("\n");

                while (mag_cmp(arb_radref(Ga), abs_tol_gamma) > 0)
                {
                    gamma_cached_prec *= 2;
                    arb_gamma_fmpq(Ga, s2, gamma_cached_prec);
                }

#if VERBOSE
                flint_printf("  lower series with N = %wd: ", NN); arb_printd(Gz0, 10); printf("\n");
#endif

                arb_sub(Gz0, Ga, Gz0, wp);

#if VERBOSE
                flint_printf("  G(a) - lower series: "); arb_printd(Gz0, 10); printf("\n");
#endif


//                arb_hypgeom_gamma_upper(Gz0, t, z0, 0, wp);
//                printf("UPPER:    "); arb_printd(Gz0, 10); printf("\n");
            }
        }
        else
        {
            arb_gamma_upper_fmpq_continuation(Gz0, s2, z0_prevn, z0, Gz0_prevn, expmz0_prevn, abs_tol_gamma, wp);
        }

#if VERBOSE
        printf("  Gz0 = "); arb_printd(Gz0, 10); printf("\n");
#endif

        if (n == 1)   /* todo!!! */
        {
            arb_neg(expmz0, z0);
            arb_exp(expmz0, expmz0, wp);
        }
        else
        {
            arb_sub(t, z0_prevn, z0, wp);
            arb_exp(t, t, wp);
            arb_mul(expmz0, expmz0_prevn, t, wp);
        }

        arb_set(z0_prevn, z0);
        arb_set(expmz0_prevn, expmz0);
        arb_set(Gz0_prevn, Gz0);

        t2 = clock();

        for (bits = start_bits * 2; bits < wp / 8; bits *= 2)
        {
            arb_extract_bits(z1, z, bits);
            arb_gamma_upper_fmpq_continuation(Gz1, s2, z0, z1, Gz0, expmz0, abs_tol_gamma, wp);

            //printf("Gz1 [%ld]: ", bits); arb_printd(Gz1, 10); printf("\n");

            arb_sub(t, z0, z1, wp);
            arb_exp(t, t, wp);
            arb_mul(expmz0, expmz0, t, wp);

            arb_set(Gz0, Gz1);
            arb_set(z0, z1);
        }

        arb_gamma_upper_fmpq_continuation(Gz1, s2, z0, z, Gz0, expmz0, abs_tol_gamma, wp);
        arb_set(Gz0, Gz1);

#if VERBOSE
        printf("  Gz0 = "); arb_printd(Gz0, 10); printf("   tol  "); mag_printd(abs_tol_gamma, 5); printf("\n");
#endif

        t3 = clock();



        //mag_t uu; mag_init(uu);
        //mag_mul_2exp_si(uu, abs_tol, 30);
        //if (mag_cmp(arb_radref(Gz0), uu) > 0)
        //    flint_abort();

        /* Compute prefactor n^-s -- todo pow_fmpq */
        arb_set_ui(ns, n);
        arb_neg(u, s_real);
        arb_pow(ns, ns, u, wp);

#if VERBOSE
        printf("  1/n^s = "); arb_printn(ns, 5, ARB_STR_NO_RADIUS); printf("\n");
#endif

        arb_mul(Gz0, Gz0, ns, wp);

#if VERBOSE
        printf("  Gz0 * pre = "); arb_printd(Gz0, 10); printf("   tol  "); mag_printd(abs_tol, 5); printf("\n");
#endif

        acb_addmul_arb(res, c, Gz0, prec);

#if VERBOSE
        printf("  sum = "); acb_printd(res, 10); printf("\n");
#endif

#if VERBOSE
        printf("  time: %f, %f\n", (t2 - t1) / CLOCKS_PER_SEC, (t3 - t2) / CLOCKS_PER_SEC);
#endif
    }

    mag_clear(err);
    mag_clear(abs_tol_gamma);
    arb_clear(s_real);
    arb_clear(ns);
    arb_clear(t);
    arb_clear(u);
    arb_clear(v);
    arb_clear(z);
    arb_clear(z0);
    arb_clear(z1);
    arb_clear(x);
    arb_clear(x2);
    arb_clear(Ga);
    arb_clear(Gz0);
    arb_clear(Gz1);
    arb_clear(expmz0);
    arb_clear(z0_prevn);
    arb_clear(Gz0_prevn);
    arb_clear(expmz0_prevn);
    acb_clear(c);
    fmpq_clear(s2);
}

#define PI 3.1415926535897932385
#define INV_LOG2 1.4426950408889634074;

/* max(pi/q,s/2)**(s/2-1) * exp(-max(pi/q,s/2)) */
static double
estimate_sum1_mag(double s, double q)
{
    return ((0.5 * s - 1) * log(FLINT_MAX(PI / q, 0.5 * s)) - FLINT_MAX(PI / q, 0.5 * s)) * INV_LOG2;
}

void
acb_dirichlet_l_fmpq_afe(acb_t res, const fmpq_t s, const dirichlet_group_t G, const dirichlet_char_t chi, slong prec)
{
    arb_t t;
    acb_t S1, S2, w;
    fmpq_t s2;
    mag_t tol1, tol2;
    double ds, m1, m2, m2pre;
    slong prec1, prec2;
    ulong q;
    int parity;

    /* Todo: implement decomposition for imprimitive characters. */
    if (G != NULL && !dirichlet_char_is_primitive(G, chi))
    {
        flint_printf("acb_dirichlet_l_fmpq_afe: a primitive character is required\n");
        acb_indeterminate(res);
        return;
    }

    q = (G == NULL) ? 1 : G->q;
    parity = (G == NULL) ? 0 : dirichlet_parity_char(G, chi);

    acb_init(S1);
    acb_init(S2);
    acb_init(w);
    arb_init(t);
    fmpq_init(s2);
    mag_init(tol1);
    mag_init(tol2);

    /* todo: correct everything below */
    ds = fmpq_get_d(s);
/*
    m1 = estimate_sum1_mag(ds + parity, q);
    m2 = estimate_sum1_mag(1.0 - ds + parity, q);
*/
    m1 = log_gamma_upper_approx(0.5 * (ds + parity), PI / q) * INV_LOG2;
    m2 = log_gamma_upper_approx(0.5 * (1.0 - ds + parity), PI / q) * INV_LOG2;

    m2pre = (ds - 0.5) * log(PI) * INV_LOG2;

    mag_one(tol1);
    mag_mul_2exp_si(tol1, tol1, FLINT_MAX(m1, m2 + m2pre) - prec);
    mag_mul_2exp_si(tol2, tol1, -m2pre);

    prec1 = prec - (FLINT_MAX(m1, m2 + m2pre) - m1);
    prec1 = FLINT_MAX(prec1, 32);

    prec2 = prec - (FLINT_MAX(m1, m2 + m2pre) - (m2 + m2pre));
    prec2 = FLINT_MAX(prec2, 32);

#if VERBOSE
    printf("mag1 = %ld   mag2 = %ld   mag2 + pre = %ld    prec, prec1, prec2 = %ld, %ld, %ld\n", (slong) m1, (slong) m2, (slong) (m2 + m2pre), prec, prec1, prec2);
    printf("tol1 = %ld   tol2 = %ld\n", MAG_EXP(tol1), MAG_EXP(tol2));

#endif

    acb_dirichlet_fmpq_sum_afe(S1, s, G, chi, tol1, prec1);

#if VERBOSE
    printf("=====================================================\n");
    printf("S1 = "); acb_printd(S1, 20); printf("  estimate = "); printf(" %g\n", ldexp(1.0, m1));
    printf("=====================================================\n");
#endif

    if (q == 1 && fmpz_is_one(fmpq_numref(s)) && fmpz_equal_ui(fmpq_denref(s), 2))
    {
        acb_mul_2exp_si(res, S1, 1);
    }
    else
    {
        /* rootnum (pi/q)^(s-1/2) sum(1-s) */
        if (fmpz_is_one(fmpq_numref(s)) && fmpz_equal_ui(fmpq_denref(s), 2))
        {
            acb_conj(S2, S1);
        }
        else
        {
            fmpq_sub_ui(s2, s, 1);
            fmpq_neg(s2, s2);
            acb_dirichlet_fmpq_sum_afe(S2, s2, G, chi, tol2, prec2);
            acb_conj(S2, S2);
        }

#if VERBOSE
        printf("=====================================================\n");
        printf("S1 = "); acb_printd(S1, 20); printf("  estimate = "); printf(" %g\n", ldexp(1.0, m1));
        printf("S2 = "); acb_printd(S2, 20); printf("  estimate = "); printf(" %g\n", ldexp(1.0, m2));
        printf("=====================================================\n");
#endif

        arb_const_pi(t, prec);
        arb_div_ui(t, t, q, prec);
        fmpq_set_si(s2, 1, 2);
        fmpq_sub(s2, s, s2);
        arb_pow_fmpq(t, t, s2, prec);
        acb_mul_arb(S2, S2, t, prec);

        if (q != 1)
        {
            acb_dirichlet_root_number2(w, G, chi, prec);
            acb_mul(S2, S2, w, prec);
        }

#if VERBOSE
        printf("S2 * prefactor = "); acb_printd(S2, 20); printf("  estimate = "); printf(" %g\n", ldexp(1.0, m2 + m2pre));
#endif

        acb_add(res, S1, S2, prec);
    }

    /* add pi^(s/2) / (s (s-1)) */
    if (q == 1)
    {
        arb_const_pi(t, prec);
        fmpq_div_2exp(s2, s, 1);
        arb_pow_fmpq(t, t, s2, prec);

        fmpq_sub_ui(s2, s, 1);
        fmpq_mul(s2, s2, s);
        arb_div_fmpz(t, t, fmpq_numref(s2), prec);
        arb_mul_fmpz(t, t, fmpq_denref(s2), prec);

        acb_add_arb(res, res, t, prec);
    }

    /* divide by gamma((s+parity)/2) */
    fmpq_add_ui(s2, s, parity);
    fmpq_div_2exp(s2, s2, 1);
    arb_gamma_fmpq(t, s2, prec);
    acb_div_arb(res, res, t, prec);

    acb_clear(S1);
    acb_clear(S2);
    acb_clear(w);
    arb_clear(t);
    fmpq_clear(s2);
    mag_clear(tol1);
    mag_clear(tol2);
}



/*

s = mpf(100.1); (nsum(lambda n: 1/n**s * gammainc(s/2, pi*n**2), [1,inf]) + pi**(s-0.5) * nsum(lambda n: 1/n**(1-s) * gammainc((1-s)/2, pi*n**2), [1,inf]) + pi**(s/2)/s/(s-1))/gamma(s/2)






estimate sum 1:
    max(pi,s/2)**(s/2-1) * exp(-max(pi,s/2))

estimate sum 2:
    pi**(s-0.5) * max(pi,(1-s)/2)**((1-s)/2-1) * exp(-max(pi,(1-s)/2))


*/

#include "flint/arith.h"

void
zeta_ui_afe(arb_t res, ulong n, slong prec)
{
    fmpq_t s;
    acb_t t;

    fmpq_init(s);
    acb_init(t);

    fmpq_set_ui(s, n, 1);
//    printf("ehu\n");
    acb_dirichlet_l_fmpq_afe(t, s, NULL, NULL, prec);
//    printf("ehua\n");
    arb_swap(res, acb_realref(t));

    fmpq_clear(s);
    acb_clear(t);
}


void
arb_bernoulli_ui_afe(arb_t b, ulong n, slong prec)
{
    slong wp, piwp;

    arb_t t, u;

    if (n < 10 || n % 2 != 0)
        flint_abort();

    wp = prec * 1.001 + 10;
    piwp = prec + 2 * FLINT_BIT_COUNT(n);

    printf("callings: %lu, %ld,  %ld, %ld\n", n, prec, wp, piwp);

    arb_init(t);
    arb_init(u);

    /* |B_n| = 2 * n! / (2*pi)^n * zeta(n) */
    arb_fac_ui(b, n, piwp);
    arb_const_pi(t, piwp);
    arb_mul_2exp_si(t, t, 1);
    arb_pow_ui(t, t, n, piwp);

    if (n > 0.7 * wp)
    {
        arb_zeta_ui_asymp(u, n, wp);
        arb_mul(b, b, u, wp);
    }
    else
    {
        zeta_ui_afe(u, n, wp);
        arb_div(t, t, u, wp);
    }

    arb_div(b, b, t, wp);
    arb_mul_2exp_si(b, b, 1);

    if (n % 4 == 0)
        arb_neg(b, b);

    arb_clear(t);
    arb_clear(u);
}


void
bernoulli_afe(fmpz_t num, fmpz_t den, ulong n)
{
    slong prec;
    arb_t t, u;

    arith_bernoulli_number_denom(den, n);

    if (n % 2)
    {
        fmpz_set_si(num, -(n == 1));
        return;
    }

    if (n < BERNOULLI_SMALL_NUMER_LIMIT)
    {
        fmpz_set_si(num, _bernoulli_numer_small[n / 2]);
        return;
    }

    arb_init(t);
    arb_init(u);

    for (prec = arith_bernoulli_number_size(n) + fmpz_bits(den) + 10; ; prec += 20)
    {
        arb_bernoulli_ui_afe(t, n, prec);
        arb_mul_fmpz(t, t, den, prec);

        if (arb_get_unique_fmpz(num, t))
            break;

        flint_printf("warning: %wd insufficient precision for Bernoulli number %wu\n", prec, n);
//        flint_abort();
        break;
    }

    arb_clear(t);
    arb_clear(u);
}

int main()
{
    acb_t res, res2;
    fmpq_t s, ss;
    slong prec;

    acb_init(res);
    acb_init(res2);
    fmpq_init(s);
    fmpq_init(ss);

#if 0
    // 10^6: 32 x 100 minutes     vs 224 seconds
    TIMEIT_ONCE_START
    bernoulli_fmpq_ui(ss, 31622);
    TIMEIT_ONCE_STOP
    TIMEIT_ONCE_START
    bernoulli_afe(fmpq_numref(s), fmpq_denref(s), 31622);
    TIMEIT_ONCE_STOP
    printf("EQUAL: %d\n", fmpq_equal(s, ss));
    return 0;
#endif

    fmpq_set_si(s, 1, 2);
    fmpq_set_si(s, 10001, 2);
    fmpq_set_si(s, 1, 2);

    fmpq_set_si(s, 4, 1);
    fmpq_set_si(s, 1, 2);
    prec = 4000;
    prec = 3333333;

    prec = 50000;
    TIMEIT_START
    acb_dirichlet_l_fmpq_afe(res, s, NULL, NULL, prec);
    TIMEIT_STOP
    TIMEIT_ONCE_START
    acb_set_fmpq(res2, s, prec);
    acb_dirichlet_l(res2, res2, NULL, NULL, prec);
    TIMEIT_ONCE_STOP

    arb_printn(acb_realref(res), prec, ARB_STR_CONDENSE * 30); printf("\n");
    arb_printn(acb_imagref(res), prec, ARB_STR_CONDENSE * 30); printf("\n");
    arb_printn(acb_realref(res2), prec, ARB_STR_CONDENSE * 30); printf("\n");
    arb_printn(acb_imagref(res2), prec, ARB_STR_CONDENSE * 30); printf("\n");

    acb_sub(res, res, res2, prec);
    acb_printn(res, 10, 0); printf("\n");
    return 0;


#if 0
    if (0)
    {
        slong N;
        mag_t tol, err;
        mag_init(err);
        mag_init(tol);
        mag_set_ui_2exp_si(tol, 1, -53);
        arb_const_pi(res2, 53);
        arb_mul_ui(res2, res2, 100, 53);
        N = gamma_lower_N(err, s, res2, tol);
        printf("N = %ld\n", N);
        gamma_lower(res, s, res2, N, 53);
        arb_printn(res, 20, 0); printf("\n");
        return 0;
    }
#endif

    dirichlet_group_t G;
    dirichlet_char_t chi;





    dirichlet_group_init(G, 5);
    dirichlet_char_init(chi, G);
    dirichlet_char_index(chi, G, 1);

    dirichlet_group_init(G, 9);
    dirichlet_char_init(chi, G);
    dirichlet_char_index(chi, G, 5);

    dirichlet_group_init(G, 1);
    dirichlet_char_init(chi, G);
    dirichlet_char_index(chi, G, 0);

    fmpq_set_si(s, 1, 2);

    double dd;
    slong d;

    for (dd = 1000000 * sqrt(10); dd <= 1000000*4 + 1; dd *= sqrt(10))
    {
        d = dd + 0.01;
        d += (d % 2);
        printf("%ld\n", d);

/*
        TIMEIT_START
        bernoulli_fmpq_ui(ss, d);
        TIMEIT_STOP
*/

        TIMEIT_START
        bernoulli_afe(fmpq_numref(s), fmpq_denref(s), d + (d % 2));
        TIMEIT_STOP
//        printf("EQUAL: %d\n", fmpq_equal(s, ss));

        return 0;
    }

    return 0;


#if 0
    for (dd = 1000000; dd <= 1000000 + 1; dd *= sqrt(10))
    {
        if (dd < 300000) continue;
        d = dd + 0.01;
        printf("%ld\n", d);
        prec = d * 3.33333333333;
        TIMEIT_START
        acb_dirichlet_l_fmpq_afe(res, s, G, chi, prec);
        TIMEIT_STOP
    }
#endif

    for (dd = 1000; dd <= 1000000 + 1; dd *= sqrt(10))
    {
        d = dd + 0.01;
        printf("%ld\n", d);
        prec = d * 3.33333333333;
        TIMEIT_START
        acb_set_fmpq(res2, s, prec);
        acb_dirichlet_l(res2, res2, G, chi, prec);
        TIMEIT_STOP
    }

/*
    for (prec = 64; ; prec *= 2)
    {
        printf("%ld\n", prec);
        TIMEIT_ONCE_START
        acb_dirichlet_zeta_fmpq_afe(res, s, prec);
        TIMEIT_ONCE_STOP
        arb_printn(res, prec, ARB_STR_CONDENSE * 30); printf("\n");
    }
*/

}


