package expression.generic;

import java.math.BigInteger;

public class BigIntegerWrapper implements NumberWrapper<BigInteger> {
    private final BigInteger data;

    public BigIntegerWrapper(int data) {
        this.data = BigInteger.valueOf(data);
    }
    public BigIntegerWrapper(BigInteger data) {
        this.data = data;
    }
    public BigIntegerWrapper(String str) {
        this.data = new BigInteger(str);
    }

    @Override
    public BigIntegerWrapper add(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.add(right.get()));
    }
    @Override
    public BigIntegerWrapper subtract(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.subtract(right.get()));
    }
    @Override
    public BigIntegerWrapper multiply(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.multiply(right.get()));
    }
    @Override
    public BigIntegerWrapper divide(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.divide(right.get()));
    }
    @Override
    public BigIntegerWrapper min(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.min(right.get()));
    }
    @Override
    public BigIntegerWrapper max(NumberWrapper<BigInteger> right) {
        return new BigIntegerWrapper(data.max(right.get()));
    }

    @Override
    public BigIntegerWrapper negate() {
        return new BigIntegerWrapper(data.negate());
    }
    @Override
    public BigIntegerWrapper count() {
        return new BigIntegerWrapper(data.bitCount());
    }

    @Override
    public BigInteger get() {
        return data;
    }

    public static class Provider implements NumberWrapperProvider<BigInteger> {
        @Override
        public NumberWrapper<BigInteger> parse(String str) {
            return new BigIntegerWrapper(str);
        }
        @Override
        public NumberWrapper<BigInteger> provide(int data) {
            return new BigIntegerWrapper(data);
        }
    }

    @Override
    public int hashCode() {
        return data.hashCode();
    }
    @Override
    public boolean equals(Object right) {
        if (right instanceof BigIntegerWrapper) {
            return data.equals(((BigIntegerWrapper)right).get());
        }
        return false;
    }
    @Override
    public String toString() {
        return data.toString();
    }
}
