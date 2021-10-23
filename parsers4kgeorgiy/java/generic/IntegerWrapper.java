package expression.generic;

import expression.exceptions.*;

public class IntegerWrapper implements NumberWrapper<Integer> {
    private int data;

    public IntegerWrapper(int data) {
        this.data = data;
    }
    @Override
    public IntegerWrapper add(NumberWrapper<Integer> right) {
        int
            r = data + right.get(),
            sl = data >> 31,
            sr = right.get() >> 31,
            sz = r >> 31;
        if (sl != sr || sz == sl) {
            return new IntegerWrapper(r);
        }
        throw new AddOverflowException();
    }

    @Override
    public IntegerWrapper subtract(NumberWrapper<Integer> right) {
        int
            rd = right.get(),
            r = data - rd,
            sl = data >> 31,
            sr = rd >> 31,
            sz = r >> 31;
        if (sl == sr || sz != sr) {
            return new IntegerWrapper(r);
        }
        throw new SubtractOverflowException();
    }
    @Override
    public IntegerWrapper multiply(NumberWrapper<Integer> right) {
        int r = right.get();
        int res = data * r;
        if (data != 0 && r != res / data || r != 0 && data != res / r) {
            throw new MultiplyOverflowException();
        }
        return new IntegerWrapper(res);
    }
    @Override
    public IntegerWrapper divide(NumberWrapper<Integer> right) {
        if (right.get() == 0) {
            throw new DivisionByZeroException();
        }
        if (right.get() == -1 && data == Integer.MIN_VALUE) {
            throw new DivideOverflowException();
        }
        return new IntegerWrapper(data / right.get());
    }
    @Override
    public IntegerWrapper min(NumberWrapper<Integer> right) {
        return new IntegerWrapper(Integer.min(data, right.get()));
    }
    @Override
    public IntegerWrapper max(NumberWrapper<Integer> right) {
        return new IntegerWrapper(Integer.max(data, right.get()));
    }

    @Override
    public IntegerWrapper negate() {
        if (data == Integer.MIN_VALUE) {
            throw new NegationOverflowException();
        }
        return new IntegerWrapper(-data);
    }
    @Override
    public IntegerWrapper count() {
        return new IntegerWrapper(Integer.bitCount(data));
    }

    @Override
    public Integer get() {
        return data;
    }

    public static class Provider implements NumberWrapperProvider<Integer> {
        @Override
        public NumberWrapper<Integer> parse(String str) {
            return new IntegerWrapper(Integer.parseInt(str));
        }
        @Override
        public NumberWrapper<Integer> provide(int data) {
            return new IntegerWrapper(data);
        }
    }

    @Override
    public int hashCode() {
        return data;
    }
    @Override
    public boolean equals(Object right) {
        if (right instanceof IntegerWrapper) {
            return data == ((IntegerWrapper)right).get();
        }
        return false;
    }
    @Override
    public String toString() {
        return Integer.toString(data);
    }
}
