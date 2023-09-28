import * as ts from 'typescript'
import {readFile, writeFile} from 'fs/promises';
import * as graph from './graph'

import assert from 'assert'

(async function() {
    const fName = process.argv.at(-2)!
    const out = process.argv.at(-1)!

    let stage = 0
    const save = async function() {
        writeFile(`${out}.${stage++}.dot`, g.toDot())
    }

    const fle = (await readFile(fName)).toString()
    const f = ts.createSourceFile(fName, fle, ts.ScriptTarget.ES2015, true);
    assert(f.statements.length == 1);
    assert(f.statements[0].kind == ts.SyntaxKind.FunctionDeclaration);

    const {g, allNames} = graph.convertFunctionToGraph(f.statements[0] as ts.FunctionDeclaration)
    save()
    graph.eliminateEmptyBB(g)
    save()
    graph.graphToSSA(g, allNames)
    save()
    graph.eliminatePhi(g)
    save()
    graph.eliminateEmptyBB(g)
    save()
})()
