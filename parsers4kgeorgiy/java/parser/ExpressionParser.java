package expression.parser;

import expression.*;
import expression.generic.IntegerWrapper;
import expression.parser.error.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;

public class ExpressionParser<T> implements Parser<T> {
    private Tokenizer<T> tokenizer;

    private void error(ParserException err) throws ParserException {
        err.setPosition(tokenizer.getPosition());
        throw err;
    }

    private CommonExpression<T> parseValue() throws ParserException {
        if (tokenizer.isEndOfScope()) {
            error(new ValueExpectedException("Unexpected end of sub-expression"));
        }
        Token<T> next = tokenizer.next();
        if (next == null) {
            error(new ValueExpectedException(tokenizer.isEOF() ? "Unexpected end of tokens" : "Unexpected token"));
        }
        if (next.type == TokenType.VALUE) {
            return ((TokenValue<T>)next).getValue();
        }
        if (next.type == TokenType.OPENBRACKET) {
            CommonExpression<T> ret = parseExpression(0);
            next = tokenizer.next();

            if (next == null || next.type != TokenType.CLOSEBRACKET) {
                error(new ParserException("Unexpected token. ')' expected"));
            }
            return ret;
        }
        if (next.type == TokenType.UNARYOPERATOR) {
            return ((TokenUnaryOperator<T>)next).provide(parseValue());
        }
        error(new ValueExpectedException("Unsupported value type"));
        return null;
    }

    private CommonExpression<T> parseExpression(int depth) throws ParserException {
        if (depth >= OperatorPriority.values().length) {
            return parseValue();
        }
        CommonExpression<T> left = parseExpression(depth + 1);
        while (true) {
            Token<T> binary = tokenizer.next();
            if (binary == null) {
                return left;
            }
            if (binary.type == TokenType.CLOSEBRACKET) {
                tokenizer.revertToken(binary);
                return left;
            }
            if (binary.type != TokenType.BINARYOPERATOR) {
                error(new BinaryOperatorExpectedException("binary operator expected, " + binary.type.toString() + " met"));
            }
            TokenBinaryOperator<T> asBin = (TokenBinaryOperator<T>)binary;
            if (asBin.getPriority() != depth) {
                tokenizer.revertToken(binary);
                return left;
            }
            CommonExpression<T> right = parseExpression(depth + 1);
            left = asBin.provide(left, right);
        }
    }

    public CommonExpression<T> parse(Tokenizer<T> tokenizer)  throws ParserException {
        if (tokenizer == null || tokenizer.isEOF()) {
            throw new IllegalArgumentException("Wrong tokenizer");
        }
        this.tokenizer = tokenizer;
        CommonExpression<T> ret = parseExpression(0);
        if (!tokenizer.isEOF()) {
            error(new ParserException("File ended before it's actual end. Check for '(' & ')'"));
        }
        return ret;
    }
}
