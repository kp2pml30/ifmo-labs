package expression.parser;

import expression.CommonExpression;
import expression.parser.error.ParserException;

public interface Parser<T> {
    CommonExpression<T> parse(Tokenizer<T> tokenizer) throws ParserException;
}
