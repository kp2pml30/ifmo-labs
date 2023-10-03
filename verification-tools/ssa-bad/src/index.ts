import * as ts from 'typescript'
import {readFile, writeFile} from 'fs/promises';
import * as graph from './graph'

import assert from 'assert'

(async function() {
    const fName = process.argv.at(-2)!
    const out = process.argv.at(-1)!

    let stage = 0
    const save = async function() {
        await writeFile(`${out}.${stage++}.dot`, g.toDot())
    }

    const fle = (await readFile(fName)).toString()
    const f = ts.createSourceFile(fName, fle, ts.ScriptTarget.ES2015, true);
    assert(f.statements.length == 1);
    assert(f.statements[0].kind == ts.SyntaxKind.FunctionDeclaration);

    const {g, allNames} = graph.convertFunctionToGraph(f.statements[0] as ts.FunctionDeclaration)
    await save()
    graph.eliminateEmptyBB(g)
    await save()
    graph.graphToSSA(g, allNames)
    await save()
    graph.eliminatePhi(g)
    await save()
    graph.eliminateEmptyBB(g)
    await save()
})()
