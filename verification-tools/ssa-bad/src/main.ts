import * as ts from 'typescript'
import * as graph from './graph'
import * as dot from 'd3-graphviz'

export function runOn(text: string, to: HTMLDivElement): void {
    const f = ts.createSourceFile('input.ts', text, ts.ScriptTarget.ES2015, true);
    graph.assert(f.statements.length == 1);
    graph.assert(f.statements[0].kind == ts.SyntaxKind.FunctionDeclaration);

    const {g, allNames} = graph.convertFunctionToGraph(f.statements[0] as ts.FunctionDeclaration)
    graph.eliminateEmptyBB(g)
    graph.graphToSSA(g, allNames)
    graph.eliminatePhi(g)
    graph.eliminateEmptyBB(g)
    dot.graphviz(to).renderDot(g.toDot())
}

(window as any)['runOn'] = runOn
