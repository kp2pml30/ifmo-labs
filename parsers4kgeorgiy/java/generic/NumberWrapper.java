package expression.generic;

public interface NumberWrapper<T> {
    public NumberWrapper<T> add(NumberWrapper<T> right);
    public NumberWrapper<T> subtract(NumberWrapper<T> right);
    public NumberWrapper<T> multiply(NumberWrapper<T> right);
    public NumberWrapper<T> divide(NumberWrapper<T> right);
    public NumberWrapper<T> min(NumberWrapper<T> right);
    public NumberWrapper<T> max(NumberWrapper<T> right);

    public NumberWrapper<T> negate();
    public NumberWrapper<T> count();

    public T get();
}
