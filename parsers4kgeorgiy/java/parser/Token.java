package expression.parser;

public class Token<T> {
    public final TokenType type;
    public final int position;
    public Token(int position, TokenType type) {
        this.position = position;
        this.type = type;
    }
}

