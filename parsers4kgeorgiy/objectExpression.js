"use strict";

const mathAdd      = (a, b) => a + b;
const mathSubtract = (a, b) => a - b;
const mathMultiply = (a, b) => a * b;
const mathDivide   = (a, b) => a / b;

function commonMulDivSimplifier(l, r) {
	if (l instanceof Negate && r instanceof Negate) {
		return new this.constructor(l.child, r.child);
	}
	if (l instanceof Const && r instanceof Negate) {
		return new this.constructor(getConst(-l.value), r.child).siplify();
	}
	if (r instanceof Const && l instanceof Negate) {
		return new this.constructor(l.child, getConst(-r.value)).siplify();
	}
	if (r.value === -1) {
		return new Negate(l).simplify();
	}
}

function emptyFunction() {}

function getInheritedClass(name, base, constructor = emptyFunction, prototypeFiller = emptyFunction) {
	const ret = function() {
		base.apply(this, arguments);
		constructor.call(this);
	}
	ret.prototype = new base();
	ret.prototype.constructor = ret
	ret.prototype.name = name;
	prototypeFiller.call(ret);
	ret.prototype.__finished = true;
	return ret;
}

function BinaryOperator(left, right) {
	if (arguments.length !== 2 && this.__finished !== undefined) {
		throw new Error("Wrong arguments count");
	}
	this.left = left;
	this.right = right;
}
BinaryOperator.prototype.evaluate = function() {
	return this.operator(
		this.left.evaluate.apply(this.left, arguments),
		this.right.evaluate.apply(this.right, arguments)
	);
}
BinaryOperator.prototype.toString = function() {
	return this.left.toString() + " " + this.right.toString() + " " + this.sign;
}
BinaryOperator.prototype.prefix = function() {
	return "(" + this.sign + " " + this.left.prefix() + " " + this.right.prefix() + ")";
}
BinaryOperator.prototype.postfix = function() {
	return "(" + this.left.postfix() + " " + this.right.postfix() + " " + this.sign + ")";
}
BinaryOperator.prototype.simplify = function() {
	let
		left = this.left.simplify(),
		right = this.right.simplify();
	if (left instanceof Const && right instanceof Const) {
		return getConst(this.operator(left.value, right.value));
	}
	return this.simplifyImpl(left, right);
}
BinaryOperator.simplifyImpl = function(l, r) { return new this.constructor(l, r); }
const Add = getInheritedClass(
	"Add",
	BinaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "+";
		this.prototype.operator = mathAdd;
		this.prototype.diff = function(name) { return new Add(this.left.diff(name), this.right.diff(name)); };
		this.prototype.simplifyImpl = function(l, r) {
			if (l.value === 0) {
				return r;
			}
			if (r.value === 0) {
				return l;
			}
			return new this.constructor(l, r);
		}
	}
);
const Subtract = getInheritedClass(
	"Subtract",
	BinaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "-";
		this.prototype.operator = mathSubtract;
		this.prototype.diff = function(name) { return new Subtract(this.left.diff(name), this.right.diff(name)); };
		this.prototype.simplifyImpl = function(l, r) {
			if (l.value === 0) {
				return new Negate(r).simplify();
			}
			if (r.value === 0) {
				return l;
			}
			if (r instanceof Cosh && r.child instanceof Subtract) {
				return new Add(l, new Cosh(r.child.right, r.child.left)).simplify();
			}
			return new this.constructor(l, r);
		}
	}
);
const Multiply = getInheritedClass(
	"Multiply",
	BinaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "*";
		this.prototype.operator = mathMultiply;
		this.prototype.diff = function(name) {
			return new Add(
				new Multiply(this.left,            this.right.diff(name)),
				new Multiply(this.left.diff(name), this.right)
			);
		};
		this.prototype.simplifyImpl = function(l, r) {
			if (l.value === 0) {
				return l;
			}
			if (r.value === 0) {
				return r;
			}
			if (l.value === 1) {
				return r;
			}
			if (r.value === 1) {
				return l;
			}
			if (l.value === -1) {
				return new Negate(r);
			}
			const com = commonMulDivSimplifier.call(this, l, r);
			if (com !== undefined) {
				return com;
			}
			return new this.constructor(l, r);
		}
	}
);
const Divide = getInheritedClass(
	"Divide",
	BinaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "/";
		this.prototype.operator = mathDivide;
		this.prototype.diff = function(name) {
			return new Divide(
				new Subtract(
					new Multiply(this.left.diff(name), this.right),
					new Multiply(this.left,            this.right.diff(name))
				),
				new Multiply(this.right, this.right)
			);
		};
		this.prototype.simplifyImpl = function(l, r) {
			if (l.value === 0 || r.value === 1) {
				return l;
			}
			let com = commonMulDivSimplifier.call(this, l, r);
			if (com !== undefined) {
				return com;
			}
			return new this.constructor(l, r);
		}
	}
);

function UnaryOperator(child) {
	if (arguments.length !== 1 && this.__finished !== undefined) {
		throw new Error("Wrong arguments count");
	}
	this.child = child;
}
UnaryOperator.prototype.evaluate = function() {
	return this.operator(this.child.evaluate.apply(this.child, arguments));
}
UnaryOperator.prototype.toString = function() {
	return this.child.toString() + " " + this.sign;
}
UnaryOperator.prototype.simplify = function() {
	const simp = this.child.simplify();
	if (simp instanceof Const) {
		return getConst(this.operator(simp));
	}
	return this.simplifyImpl(simp);
}
UnaryOperator.prototype.simplifyImpl = function(child) { return new this.constructor(child); }
UnaryOperator.prototype.prefix = function() {
	return "(" + this.sign + " " + this.child.prefix() + ")";
}
UnaryOperator.prototype.postfix = function() {
	return "(" + this.child.postfix() + " " + this.sign + ")";
}
const Negate = getInheritedClass(
	"Negate",
	UnaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "negate";
		this.prototype.operator = (x) => -x;
		this.prototype.diff = function(name) { return new Negate(this.child.diff(name)); }
		this.prototype.simplifyImpl = function(simp) {
			if (simp instanceof Negate) {
				return simp.child;
			}
			if (simp instanceof Sinh && simp.child instanceof Subtract) {
				return new Sinh(new Subtract(simp.child.right, simp.child.left));
			}
			return new Multiply(this.child, new Const(-1));
			// return new Negate(simp);
		}
	}
);
const Sinh = getInheritedClass(
	"Sinh",
	UnaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "sinh";
		this.prototype.operator = Math.sinh;
		this.prototype.diff = function(name) {
			return new Multiply(new Cosh(this.child), this.child.diff(name));
		}
	}
);
const Cosh = getInheritedClass(
	"Cosh",
	UnaryOperator,
	emptyFunction,
	function() {
		this.prototype.sign = "cosh";
		this.prototype.operator = Math.cosh;
		this.prototype.diff = function(name) {
			return new Multiply(new Sinh(this.child), this.child.diff(name));
		}
		this.prototype.simplifyImpl = function(child) {
			if (child instanceof Negate) {
				return new Cosh(child.child);
			}
			return new Cosh(child);
		}
	}
);

function Const(value) {
	this.value = value;
}
Const.prototype.evaluate = function() { return this.value; };
Const.prototype.toString = function() { return this.value.toString() };
Const.prototype.prefix   = Const.prototype.toString;
Const.prototype.postfix  = Const.prototype.toString;
Const.prototype.diff     = function() { return getConst(0); };
Const.prototype.simplify = function() { return this; };

function NaryOperation() {
	this.children = Array.prototype.slice.call(arguments);
}
NaryOperation.prototype.postfix = function() {
	if (this.children.length === 0) {
		return "( " + this.sign + ")"
	}
	return "(" + this.children.reduce((accum, child) => accum + child.postfix() + " ", "") + this.sign + ")";
}
const Sum = getInheritedClass(
	"Sum",
	NaryOperation,
	emptyFunction,
	function() {
		this.prototype.sign = "sum";
		this.prototype.evaluate = function() {
			return this.children.reduce((accum, x) => accum + x.evaluate(...arguments), 0);
		};
		this.prototype.diff = function() {
			return new Sum(...this.children.map(x => x.diff(...arguments)));
		};
	}
);
const Avg = getInheritedClass(
	"Avg",
	NaryOperation,
	emptyFunction,
	function() {
		this.prototype.sign = "avg";
		this.prototype.evaluate = function() {
			return this.children.reduce((accum, x) => accum + x.evaluate(...arguments), 0) / this.children.length;
		};
		this.prototype.diff = function() {
			return new Avg(...this.children.map(x => x.diff(...arguments)));
		};
	}
);
function getConst(value) {
	if (value === 0) {
		return getConst.prototype.zero;
	}
	if (value === 1) {
		return getConst.prototype.one;
	}
	return new Const(value);
}
getConst.prototype.zero = new Const(0);
getConst.prototype.one  = new Const(1);

function Variable(name) {
	if (name !== "x" && name !== "y" && name !== "z") {
		throw new Error("Unsupported variable name " + name);
	}
	this.name = name;
}
Variable.prototype.evaluate = function(x, y, z) {
  return this.name === "x" ? x : this.name === "y" ? y : this.name === "z" ? z : undefined;
}
Variable.prototype.diff = function(name) { return getConst(this.name === name ? 1 : 0); };
Variable.prototype.toString = function() { return this.name.toString(); };
Variable.prototype.prefix = Variable.prototype.toString;
Variable.prototype.postfix = Variable.prototype.toString;
Variable.prototype.simplify = function() { return this; };

const variables = new Set(["x", "y", "z"]);

function parser(arr) {
	const binary = {"+": Add, "-": Subtract, "*": Multiply, "/": Divide};
	const functions = {"sinh": Sinh, "cosh": Cosh};
	const ret = arr.reduce((stack, cur) => {
		if (cur === "negate") {
			if (stack.length === 0) {
				throw new Error("bad negate");
			}
			stack.push(new Negate(stack.pop()));
			return stack;
		}
		const asflt = Number.parseFloat(cur);
		if (!isNaN(asflt)) {
			stack.push(getConst(asflt));
			return stack;
		}
		const func = functions[cur];
		if (func !== undefined) {
			if (!stack.length) {
				throw new Error("Bad unary function");
			}
			stack.push(new func(stack.pop()));
		} else if (variables.has(cur)) {
			stack.push(new Variable(cur));
		} else {
			const bin = binary[cur];
			if (bin !== undefined) {
				if (stack.length < 2) {
					throw new Error("Bad binary operator");
				}
				const b = stack.pop(), a = stack.pop();
				stack.push(new bin(a, b));
				return stack;
			}
			throw new Error("unknown token $" + cur + "$");
		}
		return stack;
	}, []);
	if (ret.length !== 1) {
		throw new Error("wrong expression");
	}
	return ret[0];
}

function _getLength(str, pos, checker) {
	if (pos >= str.length || !checker(str.charAt(pos))) {
		return 0;
	}
	return 1 + _getLength(str, pos + 1, checker);
}
function _skipWS(str, pos) {
	return pos + _getLength(str, pos, cha => /\s/.test(cha));
}
function _throwException(str, pos) {
	const ret = new Error(str + " at " + pos.toString());
	// ret.position = position;
	throw ret;
}

function clojureParser() {
}
clojureParser.prototype.operatorNames = {"negate": Negate, "sum": Sum, "avg": Avg};
clojureParser.prototype.parseNumber = function(str, pos) {
	const num = parseInt(str.substring(pos));
	if (Number.isNaN(num))
		return null;
	return [getConst(num), num.toString().length];

	_throwException("Number parsing failed", pos);
}
clojureParser.prototype.parseVariable = function(str, pos) {
	const len = _getLength(str, pos, cha => /[a-zA-Z]/.test(cha));
	if (len === 0) {
		return null;
	}
	const name = str.substring(pos, pos + len);
	if (this.operatorNames[name] !== undefined) {
		return null;
	}
	return [new Variable(name), len];
}
clojureParser.prototype.parseValue = function(str, pos) {
	const val = this.parseNumber(str, pos);
	if (val !== null) {
		return val;
	}
	const varb = this.parseVariable(str, pos);
	if (varb !== null)
		return varb;
	return this.parseClojure(str, pos);
}
clojureParser.prototype.parseOperation = function(str, pos) {
	if (pos >= str.length) {
		return null;
	}
	const wordLen = _getLength(str, pos, cha => /[a-zA-Z]/.test(cha));
	const operatorName = this.operatorNames[str.substring(pos, pos + wordLen)];
	if (operatorName !== undefined) {
		return [operatorName, wordLen];
	}
	const binary = {"+": Add, "-": Subtract, "*": Multiply, "/": Divide};
	const found = binary[str.charAt(pos)];
	if (found !== undefined) {
		return [found, 1];
	}
	return null;
}
clojureParser.prototype.parseValues = function(str, pos) {
	const next = this.parseValue(str, pos);
	if (next === null) {
		return [[], 0];
	}
	const wsSkipped = _skipWS(str, pos + next[1]);
	const following = this.parseValues(str, wsSkipped);
	following[0].unshift(next[0]);
	return [following[0], wsSkipped - pos + following[1]];
}
clojureParser.prototype.parseClojure = function(str, pos) {
	const pos0 = pos;
	// it is possible to convert pos to SSA, but program is linear => it is useless
	if (pos >= str.length || str.charAt(pos) !== '(') {
		return null;
	}
	pos += 1;
	pos = _skipWS(str, pos);
	const oper = this.parseOperation(str, pos);
	if (oper === null) {
		_throwException("Operation expected", pos);
	}
	const prev = pos + oper[1];
	pos = _skipWS(str, pos + oper[1]);
	const values = this.parseValues(str, pos);
	if (pos - prev === 0 && values[0].length > 0 && !(values[0][0] instanceof BinaryOperator) && !(values[0][0] instanceof UnaryOperator)) {
		_throwException("Operation and operand must be ws separated", pos);
	}
	if (values === null) {
		_throwException("Empty operator call", pos);
	}
	pos = _skipWS(str, pos + values[1]);
	if (pos >= str.length || str.charAt(pos) !== ')') {
		_throwException("')' expected for clojure", pos);
	}
	let operation;
	try {
		operation = new oper[0](...values[0]);
	} catch (exc) {
		_throwException("Operator creation failed. " + exc.toString(), pos);
	}
	return [operation, _skipWS(str, pos + 1) - pos0];
}

clojureParser.prototype.parseProgram = function(str) {
	const skipped = _skipWS(str, 0);
	if (skipped === str.length) {
		_throwException("Empty input", skipped);
	}
	var ret = this.parseValue(str, skipped);
	if (ret === null) {
		_throwException("Wrong input: single value expected", skipped);
	}
	ret[1] = _skipWS(str, skipped + ret[1]);
	if (ret[1] !== str.length) {
		_throwException("Unreachable tokens", ret[1]);
	}
	return ret[0];
}

const clojurePostfixParser = getInheritedClass(
	"clojurePostfixParser",
	clojureParser
);
clojurePostfixParser.prototype.parseClojure = function(str, pos) {
	const pos0 = pos;
	if (pos >= str.length || str.charAt(pos) !== '(') {
		return null;
	}
	pos += 1;
	pos = _skipWS(str, pos);
	const values = this.parseValues(str, pos);
	if (values === null) {
		_throwException("Empty operator call", pos);
	}
	pos = _skipWS(str, pos + values[1]);
	const oper = this.parseOperation(str, pos);
	if (oper === null) {
		_throwException("Operation expected", pos);
	}
	pos = _skipWS(str, pos + oper[1]);
	if (pos >= str.length || str.charAt(pos) !== ')') {
		_throwException("')' expected for clojure", pos);
	}
	let operation;
	try {
		operation = new oper[0](...values[0]);
	} catch (exc) {
		_throwException("Operator creation failed. " + exc.toString(), pos);
	}
	return [operation, _skipWS(str, pos + 1) - pos0];
}

const parsePrefix = input => new clojureParser().parseProgram(input);

const parsePostfix = input => new clojurePostfixParser().parseProgram(input);

const parse = input => parser(input.trim().split(/\s+/));

// alert(new Sum().postfix())
