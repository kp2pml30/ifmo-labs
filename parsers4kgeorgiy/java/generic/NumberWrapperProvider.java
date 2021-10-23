package expression.generic;

public interface NumberWrapperProvider<T> {
    public NumberWrapper<T> parse(String from);
    public NumberWrapper<T> provide(int data);
}
