package org.libpetri.smt.z3;

import java.math.BigInteger;
import java.util.Objects;

/**
 * An exact rational number over unbounded integers, always in lowest terms with a positive
 * denominator. The arithmetic of the colour-slot linear program ([NU-053], {@link SlotBoundLp}):
 * no floating point, and no fixed-width integer that could overflow, so every implementation
 * computes the same values.
 *
 * <p>{@link #toString()} prints {@code n} for an integer and {@code n/d} otherwise, the form the
 * report line and the shared parity file use.
 */
public final class Rational implements Comparable<Rational> {

    /** Zero. */
    public static final Rational ZERO = new Rational(BigInteger.ZERO, BigInteger.ONE);

    /** One. */
    public static final Rational ONE = new Rational(BigInteger.ONE, BigInteger.ONE);

    private final BigInteger num;
    private final BigInteger den;

    private Rational(BigInteger num, BigInteger den) {
        this.num = num;
        this.den = den;
    }

    /** {@code num / den} in lowest terms. Throws {@link ArithmeticException} when {@code den} is zero. */
    public static Rational of(BigInteger num, BigInteger den) {
        if (den.signum() == 0) {
            throw new ArithmeticException("Rational with a zero denominator");
        }
        BigInteger g = num.gcd(den);
        if (!g.equals(BigInteger.ONE)) {
            num = num.divide(g);
            den = den.divide(g);
        }
        if (den.signum() < 0) {
            num = num.negate();
            den = den.negate();
        }
        return new Rational(num, den);
    }

    /** The integer {@code value}. */
    public static Rational of(BigInteger value) {
        return new Rational(value, BigInteger.ONE);
    }

    /** The integer {@code value}. */
    public static Rational of(long value) {
        return new Rational(BigInteger.valueOf(value), BigInteger.ONE);
    }

    /** {@code num / den} in lowest terms. */
    public static Rational of(long num, long den) {
        return of(BigInteger.valueOf(num), BigInteger.valueOf(den));
    }

    /** The numerator, in lowest terms. */
    public BigInteger numerator() {
        return num;
    }

    /** The denominator, in lowest terms and positive. */
    public BigInteger denominator() {
        return den;
    }

    /** {@code -1}, {@code 0} or {@code 1}. */
    public int signum() {
        return num.signum();
    }

    public boolean isZero() {
        return num.signum() == 0;
    }

    public Rational negate() {
        return new Rational(num.negate(), den);
    }

    public Rational add(Rational o) {
        if (den.equals(o.den)) {
            return of(num.add(o.num), den);
        }
        return of(num.multiply(o.den).add(o.num.multiply(den)), den.multiply(o.den));
    }

    public Rational subtract(Rational o) {
        return add(o.negate());
    }

    public Rational multiply(Rational o) {
        if (num.signum() == 0 || o.num.signum() == 0) {
            return ZERO;
        }
        return of(num.multiply(o.num), den.multiply(o.den));
    }

    /** {@code this / o}. Throws {@link ArithmeticException} when {@code o} is zero. */
    public Rational divide(Rational o) {
        if (o.num.signum() == 0) {
            throw new ArithmeticException("division by zero");
        }
        return of(num.multiply(o.den), den.multiply(o.num));
    }

    @Override
    public int compareTo(Rational o) {
        return num.multiply(o.den).compareTo(o.num.multiply(den));
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof Rational r && num.equals(r.num) && den.equals(r.den);
    }

    @Override
    public int hashCode() {
        return Objects.hash(num, den);
    }

    @Override
    public String toString() {
        return den.equals(BigInteger.ONE) ? num.toString() : num + "/" + den;
    }
}
