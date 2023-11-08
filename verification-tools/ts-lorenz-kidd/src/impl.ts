import * as ts from 'typescript'

const SUBST_NAME = '___123.ts'

function assert<T extends boolean>(x: T, msg?: any): T extends false ? never : void {
    if (x == false) {
        throw new Error(`assertion failed ${msg}`)
    } else {
        return undefined as any
    }
}

export function programFromText(txt: string): ts.Program {
    const compilerOptions = {}
    const compilerHost = ts.createCompilerHost(compilerOptions);
    const f = ts.createSourceFile(SUBST_NAME, txt, ts.ScriptTarget.ES2015, true);
    const old = compilerHost.getSourceFile;
    compilerHost.getSourceFile = (fileName: string, languageVersionOrOptions: ts.ScriptTarget | ts.CreateSourceFileOptions, onError?: (message: string) => void, shouldCreateNewSourceFile?: boolean): ts.SourceFile | undefined => {
        if (fileName == SUBST_NAME) {
            return f
        }
        return old.call(compilerHost, fileName, languageVersionOrOptions, onError, shouldCreateNewSourceFile);
    };
    return ts.createProgram([SUBST_NAME], compilerOptions, compilerHost);
}

class ClassMetricsData {
    methodsCount = 0
    overriddenMethods = 0
    propertiesCount = 0
    abstract = false
    depth = 0
    selfProps = 0
    onlySelfProps = 0
    baseProps = 0
}

class MethodMetricsData {
    complexity = 0
    averageMethodParams = 0
}


class Walker {
    checker: ts.TypeChecker

    constructor(checker: ts.TypeChecker) {
        this.checker = checker
    }

    ret = {
        classMetricsData: {} as { [key: string]: ClassMetricsData },
        methodMetricsData: {} as { [key: string]: MethodMetricsData },
        projectMetricsData: {
            classesCount: 0,
            keyClasses: 0
        }
    }

    exprCost(e: ts.Expression, callsComplexity: {callParamsSum: number, callsCount: number}): number {
        if (ts.isBinaryExpression(e)) {
            const tokText = e.operatorToken.getText()
            const cost = tokText.charAt(0) == "=" && tokText.charAt(1) != "=" ? 0.5 : 2
            return cost + this.exprCost(e.left, callsComplexity) + this.exprCost(e.right, callsComplexity)
        }
        if (ts.isPrefixUnaryExpression(e)) {
            return 2 + this.exprCost(e.operand, callsComplexity)
        }
        if (ts.isPostfixUnaryExpression(e)) {
            return 2 + this.exprCost(e.operand, callsComplexity)
        }
        if (ts.isLiteralExpression(e) || ts.isIdentifier(e)) {
            return 0
        }
        if (ts.isParenthesizedExpression(e)) {
            return this.exprCost(e.expression, callsComplexity)
        }
        if (ts.isConditionalExpression(e)) {
            return this.exprCost(e.condition, callsComplexity) + this.exprCost(e.whenTrue, callsComplexity) + this.exprCost(e.whenFalse, callsComplexity)
        }
        if (ts.isCallExpression(e) || ts.isNewExpression(e)) {
            const symbol = this.checker.getSymbolAtLocation(e.expression)
            //assert(!!this.checker.getSymbolAtLocation(e))
            const decorators = symbol?.getDeclarations()?.flatMap(x => ts.getDecorators(x as ts.MethodDeclaration) || []) || []
            const isApi: boolean = !!decorators?.find(x => ts.isIdentifier(x.expression) ? (x.expression.getText() == "ApiCall") : false)
            //console.log(isApi, decorators)
            const cost = isApi ? 7 : 5
            if (isApi) {
                callsComplexity.callParamsSum += e.arguments?.length || 0
                callsComplexity.callsCount += 1
            }
            return cost + (e.arguments?.reduce((v, c) => v + this.exprCost(c, callsComplexity), 0) || 0)
        }
        return assert(false, e.kind)
    }

    statementCost(s: ts.Statement | ts.Expression, callsComplexity: {callParamsSum: number, callsCount: number}): number {
        if (ts.isExpression(s)) {
            return this.exprCost(s, callsComplexity)
        }
        if (ts.isVariableDeclaration(s)) {
            const init = s.initializer
            return 0.5 + (init ? this.exprCost(init, callsComplexity) : 0)
        }
        if (ts.isExpressionStatement(s)) {
            return this.exprCost(s.expression, callsComplexity)
        }
        let ret = 0
        ts.forEachChild(s, s => ret += this.statementCost(s as ts.Statement | ts.Expression, callsComplexity))
        return ret
    }

    visitMethod(meth: ts.MethodDeclaration) {
        if (!meth.body) {
            return
        }
        const metric = new MethodMetricsData()
        metric.complexity += meth.parameters.length * 0.3
        const callsComplexity = {callParamsSum: 0, callsCount: 0}
        metric.complexity += this.statementCost(meth.body, callsComplexity)
        const name = this.checker.getFullyQualifiedName(this.checker.getTypeAtLocation(meth).symbol!)
        metric.averageMethodParams = callsComplexity.callParamsSum / callsComplexity.callsCount
        if (isNaN(metric.averageMethodParams)) {
            metric.averageMethodParams = 0
        }
        this.ret.methodMetricsData[name] = metric
    }

    private getSelfProperties(to: Array<string>, klass: { readonly heritageClauses?: ts.NodeArray<ts.HeritageClause>, members?: ts.NodeArray<ts.ClassElement | ts.TypeElement> }) {
        for (const m of klass.members || []) {
            const n = m.name
            if (n) {
                to.push(n.getText())
            }
        }
    }

    iterateBases<T extends { readonly heritageClauses?: ts.NodeArray<ts.HeritageClause> }>(klass: T, foo: (x: T) => void): void {
        for (const h of klass.heritageClauses || []) {
            for (const t of h.types) {
                const type = this.checker.getTypeAtLocation(t.expression)
                const decl = type.getSymbol()?.getDeclarations() || []
                assert(decl.length == 1, `len = ${decl.length}`)
                foo(decl[0] as any)
            }
        }
    }

    private getAllProperties(to: Array<string>, klass: { readonly heritageClauses?: ts.NodeArray<ts.HeritageClause>, members: ts.NodeArray<ts.ClassElement | ts.TypeElement> }) {
        const foo = (klass: { readonly heritageClauses?: ts.NodeArray<ts.HeritageClause>, members: ts.NodeArray<ts.ClassElement | ts.TypeElement> }) => {
            this.iterateBases(klass, foo)
            this.getAllProperties(to, klass)
        }
        this.iterateBases(klass, foo)

        this.getSelfProperties(to, klass)
    }

    visitClass(klass: ts.ClassDeclaration) {
        this.ret.projectMetricsData.classesCount += 1
        if (ts.getDecorators(klass)?.find(x => ts.isIdentifier(x.expression) && x.expression.getText() == "KeyClass")) {
            this.ret.projectMetricsData.keyClasses += 1
        }
        const metric = new ClassMetricsData()
        const baseProps: string[] = []
        this.iterateBases(klass, (klass: any) => this.getAllProperties(baseProps, klass))
        const selfProps: string[] = []
        this.getSelfProperties(selfProps, klass)
        metric.selfProps = selfProps.length
        metric.baseProps = baseProps.length
        metric.onlySelfProps = selfProps.filter(x => !baseProps.includes(x)).length
        //classMetric.abstract = klass.modifiers?.some(x => x.kind == ts.SyntaxKind.OverrideKeyword) || false
        metric.abstract = (ts.getCombinedModifierFlags(klass) & ts.ModifierFlags.Abstract) != 0
        //classMetric.abstract = (this.checker.getTypeAtLocation(klass).flags & ts.TypeFlags.StructuredOrInstantiable) == 0

        const getDepth = (klass: ts.ClassLikeDeclaration, i = 0): number => {
            //assert(ts.isClassDeclaration(klass), klass.kind)
            if (klass.heritageClauses) {
                for (const x of klass.heritageClauses.filter(a => a.token == ts.SyntaxKind.ExtendsKeyword)) {
                    for (const t of x.types) {
                        return getDepth(t.expression as any, i + 1)
                    }
                }
            }
            return i
        }
        //console.log("===========")
        metric.depth = getDepth(klass)

        ts.forEachChild(klass, node => {
            if (ts.isMethodDeclaration(node)) {
                metric.methodsCount += 1
                //const sig = this.checker.getSignatureFromDeclaration(m)?.getDeclaration() as ts.MethodSignature
                if (baseProps.includes(node.name.getText())) {
                    metric.overriddenMethods += 1
                }
                this.visitMethod(node)
            }
            if (ts.isPropertyDeclaration(node)) {
                metric.propertiesCount += 1
            }
        })
        const name = this.checker.getFullyQualifiedName(this.checker.getTypeAtLocation(klass).symbol!)
        this.ret.classMetricsData[name] = metric
    }

    visitFile(f: ts.SourceFile) {
        ts.forEachChild(f, node => {
            ts.SyntaxKind
            if (ts.isClassDeclaration(node)) {
                this.visitClass(node)
            }
        })
    }
}

export type FinalMetric = {
    fullName: string,
    value: any,
    ok: boolean,
    reason: string
}

function okAndFail(ctx: any, x: string): {ok: boolean, reason: string} {
    const ok = eval(x)
    const reason = x.replace(/\bctx\./g, '')
    return {ok, reason}
}

export function calcClassMetrics(inp: ClassMetricsData): { [key: string]: FinalMetric } {
    //assert(inp.onlySelfProps == inp.selfProps - inp.baseProps, `${inp.onlySelfProps} == ${inp.selfProps} - ${inp.baseProps}`)
    let noa = inp.onlySelfProps
    //if (noa < 0) noa = 0
    const si = (inp.overriddenMethods * inp.depth) / (inp.selfProps)
    return {
        "cs": {
            fullName: "class size",
            value: inp.methodsCount + inp.propertiesCount,
            ...okAndFail(inp, "ctx.methodsCount <= 20")
        },
        "depth": {
            fullName: "extends length",
            value: inp.depth,
            ok: true,
            reason: ""
        },
        "noo": {
            fullName: "number of overridden operations",
            value: inp.overriddenMethods,
            ...okAndFail(inp, "ctx.overriddenMethods <= 3")
        },
        "noa": {
            fullName: "number of operations added by a subclass",
            value: noa,
            ...okAndFail({noa}, "ctx.noa <= 4")
        },
        "si": {
            fullName: "specialization index",
            value: si,
            ...okAndFail({si}, "ctx.si <= 0.75")
        }
    }
}

export function calcMethodMetrics(inp: MethodMetricsData): { [key: string]: FinalMetric } {
    return {
        "oc": {
            fullName: "operation complexity",
            value: inp.complexity,
            ...okAndFail(inp, "ctx.complexity <= 65")
        },
        "np_avg": {
            fullName: "average number of parameters per operation",
            value: inp.averageMethodParams,
            ...okAndFail(inp, "ctx.averageMethodParams <= 0.7")
        }
    }
}

export function analyze(prog: ts.Program): Walker['ret'] {
    const checker = prog.getTypeChecker()
    const src: ts.SourceFile = prog.getSourceFile(SUBST_NAME)!
    const w = new Walker(checker)
    w.visitFile(src)
    return w.ret
}
