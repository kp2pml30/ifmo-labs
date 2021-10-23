package expression.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.List;
import java.util.Map;
import java.util.Set;

import expression.*;
import expression.parser.error.*;
import expression.generic.NumberWrapperProvider;

public class Tokenizer<T> {
    private final String str;
    private boolean waitForValue;
    private int position;
    private Token<T> previousToken;
    private int positionBeforeRevert;

    private NumberWrapperProvider<T> constantFormatter;

    private final Map<String, BinaryOperator.Provider<T>> binaryOperator = Map.of("+", new Add.MyProvider<T>(), "-", new Subtract.MyProvider<T>(), "*", new Multiply.MyProvider<T>(), "/", new Divide.MyProvider<T>(), "min", new Min.MyProvider<T>(), "max", new Max.MyProvider<T>());
    private final Map<String, UnaryOperator.Provider<T>> unaryOperator = Map.of("-", new UnaryMinus.MyProvider<T>(), "count", new Count.MyProvider<T>());
    private final Map<Character, List<String>> operators = Map.of('+', List.of("+"), '-', List.of("-"), '*', List.of("*"), '/', List.of("/"), 'c', List.of("count"), 'm', List.of("max", "min"));
    private final Map<Character, Brackets<T>> brackets = Map.of('(', new Brackets<T>(true), ')', new Brackets<T>(false));

    public Tokenizer(final String expr, final NumberWrapperProvider<T> provider) {
        str = expr;
        position = 0;
        waitForValue = true;
        constantFormatter = provider;
    }

    /*** utilities ***/
    private void error(ParserException err) throws ParserException {
        err.setPosition(position);
        throw err;
    }
    /*** tokens parser ***/
    private void skipWhitespace() {
        while (position < str.length() && Character.isWhitespace(str.charAt(position))) {
            position++;
        }
    }

    private TokenValue<T> scanConst() throws ParserException {
        if (!waitForValue || position >= str.length()) {
            return null;
        }
        int cur = position;
        int unary = 0;
        if (str.charAt(cur) == '-' || str.charAt(cur) == '+') {
            unary = 1;
            cur++;
        } else if (str.charAt(cur) == '+') {
            unary = 1;
            cur++;
        }
        while (cur < str.length() && Character.isDigit(str.charAt(cur))) {
            cur++;
        }
        if (cur > position + unary) {
            TokenValue<T> ret = null;
            try {
                ret = new TokenValue<T>(position, new Const<T>(constantFormatter.parse(str.substring(position, cur))));
            } catch (NumberFormatException numberFormatException) {
                error(new expression.parser.error.ConstantFormatException(numberFormatException.toString(), position));
            }
            position = cur;
            waitForValue = false;
            return ret;
        }
        return null;
    }

    private TokenValue<T> scanVariable() {
        int cur = position;
        while (cur < str.length() && Character.isAlphabetic(str.charAt(cur))) {
            cur++;
        }
        if (cur > position) {
            TokenValue<T> ret = new TokenValue<T>(position, new Variable<T>(str.substring(position, cur)));
            position = cur;
            waitForValue = false;
            return ret;
        }
        return null;
    }

    private Token<T> scanOperator() throws ParserException {
        final int leftlen = str.length() - position;
        if (leftlen <= 0) {
            return null;
        }
        List<String> possible = operators.get(str.charAt(position));
        if (possible == null) {
            return null;
        }
        String chosen = null;
        for (String cur : possible) {
            if (cur.length() > leftlen) {
                continue;
            }
            if (str.substring(position, position + cur.length()).equals(cur)) {
                int indCheck = position + cur.length();
                if (Character.isAlphabetic(cur.charAt(0)) && indCheck < str.length() && Character.isAlphabetic(str.charAt(indCheck))) {
                    continue;
                }
                chosen = cur;
                break;
            }
        }
        if (chosen == null) {
            return null;
        }
        Token<T> ret = null;
        if (waitForValue) {
            UnaryOperator.Provider<T> provider = unaryOperator.get(chosen);
            if (provider == null) {
                return null;
            }
            ret = new TokenUnaryOperator<T>(position, provider);
        } else {
            BinaryOperator.Provider<T> prov = binaryOperator.get(chosen);
            if (prov == null) {
                return null;
            }
            ret = new TokenBinaryOperator<T>(position, prov);
            waitForValue = true;
        }
        position += chosen.length();
        return ret;
    }

    private Token<T> scanBracket() throws ParserException {
        if (position >= str.length()) {
            return null;
        }
        char chr = str.charAt(position);
        if (chr == '(') {
            if (!waitForValue) {
                error(new BinaryOperatorExpectedException("Function call is not supported"));
            }
            position++;
            return new Token<T>(position, TokenType.OPENBRACKET);
        } else if (chr == ')') {
            if (waitForValue) {
                error(new ValueExpectedException("unexpected ')'"));
            }
            position++;
            return new Token<T>(position, TokenType.CLOSEBRACKET);
        }
        return null;
    }

    public void revertToken(Token<T> element) {
        if (previousToken != null) {
            throw new IllegalStateException("Previous token in tokenizer is already set");
        }
        previousToken = element;
        positionBeforeRevert = position;
        position = element.position;
    }

    public Token<T> next() throws ParserException {
        if (previousToken != null) {
            Token<T> ret = previousToken;
            previousToken = null;
            position = positionBeforeRevert;
            return ret;
        }
        skipWhitespace();
        if (position == str.length()) {
            return null;
        }
        Token<T> res;
        if (waitForValue) {
            res = scanConst();
            if (res != null) {
                return res;
            }
            res = scanOperator();
            if (res != null) {
                return res;
            }
            res = scanVariable();
            if (res != null) {
                return res;
            }
        } else {
            res = scanOperator();
            if (res != null) {
                return res;
            }
        }
        res = scanBracket();
        if (res == null && waitForValue) {
            int oldPosition = position;
            waitForValue = false;
            Token<T> check = scanOperator();
            position = oldPosition;
            if (check != null) {
                error(new ValueExpectedException("This unary operator is not supported"));
            }
            return null;
        }
        return res;
    }

    /*** end of stream checkers ***/
    public boolean isEOF() {
        if (previousToken != null) {
            return false;
        }
        skipWhitespace();
        return position >= str.length();
    }

    public boolean isEndOfScope() {
        return isEOF() || str.charAt(position) == ')';
    }

    /*** utility ***/
    public int getPosition() {
        return position;
    }

    public String getSlice() {
        if (position >= str.length()) {
            return "";
        }
        return str.substring(position);
    }

    public String getSlice(int length) {
        if (position >= str.length()) {
            return "";
        }
        if (position + length > str.length()) {
            return str.substring(position);
        } else {
            return str.substring(position + length);
        }
    }
}
