package expression.parser;
import expression.Value;

public class TokenValue<T> extends Token<T> {
    private final Value<T> value;
    public TokenValue(int position, Value<T> value) {
        super(position, TokenType.VALUE);
        this.value = value;
    }

    public Value<T> getValue() {
        return value;
    }
}
