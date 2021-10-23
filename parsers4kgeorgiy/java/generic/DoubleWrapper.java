package expression.generic;

public class DoubleWrapper implements NumberWrapper<Double> {
    private double data;

    public DoubleWrapper(int data) {
        this.data = data;
    }
    public DoubleWrapper(double data) {
        this.data = data;
    }
    @Override
    public DoubleWrapper add(NumberWrapper<Double> right) {
        return new DoubleWrapper(data + right.get());
    }

    @Override
    public DoubleWrapper subtract(NumberWrapper<Double> right) {
        return new DoubleWrapper(data - right.get());
    }
    @Override
    public DoubleWrapper multiply(NumberWrapper<Double> right) {
        return new DoubleWrapper(data * right.get());
    }
    @Override
    public DoubleWrapper divide(NumberWrapper<Double> right) {
        return new DoubleWrapper(data / right.get());
    }
    @Override
    public DoubleWrapper min(NumberWrapper<Double> right) {
        return new DoubleWrapper(Double.min(data, right.get()));
    }
    @Override
    public DoubleWrapper max(NumberWrapper<Double> right) {
        return new DoubleWrapper(Double.max(data, right.get()));
    }

    @Override
    public DoubleWrapper negate() {
        return new DoubleWrapper(-data);
    }
    @Override
    public DoubleWrapper count() {
        return new DoubleWrapper((double)Long.bitCount(Double.doubleToLongBits(data)));
    }

    @Override
    public Double get() {
        return data;
    }

    public static class Provider implements NumberWrapperProvider<Double> {
        @Override
        public NumberWrapper<Double> parse(String str) {
            return new DoubleWrapper(Integer.parseInt(str));
        }
        @Override
        public NumberWrapper<Double> provide(int data) {
            return new DoubleWrapper(data);
        }
    }

    @Override
    public int hashCode() {
        return Double.hashCode(data);
    }
    @Override
    public boolean equals(Object right) {
        if (right instanceof DoubleWrapper) {
            return data == ((DoubleWrapper)right).get();
        }
        return false;
    }
    @Override
    public String toString() {
        return Double.toString(data);
    }
}
