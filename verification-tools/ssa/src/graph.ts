import * as ts from 'typescript'
import assert from 'assert'

export class Inst {
    bb: BBlock
    id: number
    op: string
    inputs: Inst[] = []
    inputsNames: string[] | undefined = undefined
    users: Inst[] = []

    constructor(bb: BBlock, id: number, op: string) {
        this.bb = bb
        this.id = id
        this.op = op
    }

    addInput(...inp: Inst[]): void {
        this.inputs.push(...inp)
        for (const i of inp) {
            i.users.push(this)
        }
    }

    replaceUsers(w: Inst): void {
        w.users.push(...this.users)
        for (const u of this.users) {
            u.inputs = u.inputs.map((x) => x == this ? w : x)
        }
    }
}

export class BBlock {
    private graph: Graph
    id: number

    constructor(graph: Graph) {
        this.graph = graph
        this.id = graph.next_bb++
    }

    inst(op: string): Inst {
        const r = new Inst(this, this.graph.next_inst++, op)
        this.insts.push(r);
        return r;
    }

    phi(name: string): Inst {
        const r = new Inst(this, this.graph.next_inst++, `phi_${name}`)
        this.insts.splice(0, 0, r)
        return r
    }

    addSucc(...bbs: BBlock[]) {
        assert(this.succs.length == 0)
        this.succs.push(...bbs)
        for (const b of bbs) {
            b.preds.push(this)
        }
    }

    insts: Inst[] = []
    succs: BBlock[] = []
    preds: BBlock[] = []
}

export class Graph {
    blocks: BBlock[] = []
    next_bb = 0
    next_inst = 0
    entry: BBlock = this.bb()

    constructor() {
        this.entry.inst("__entry")
    }

    bb(): BBlock {
        const r = new BBlock(this)
        this.blocks.push(r)
        return r
    }

    toDot(): string {
        const builder: string[] = []
        builder.push('digraph G {\ncompound=true;\nnode[shape=plaintext];\n')
        for (const from of this.blocks) {
            if (from.insts.length == 0) {
                from.inst('__entry')
            }
        }
        for (const from of this.blocks) {
            for (const to of from.succs) {
                const f = from.insts[from.insts.length - 1]
                const t = to.insts[0]
                builder.push(`inst_${f.id}:res:s -> inst_${t.id}:res:n [ltail=cluster_BB${from.id}, lhead=cluster_BB${to.id}, color=red];`)
            }
        }
        builder.push("\n\n")
        for (const b of this.blocks) {
            builder.push(`subgraph cluster_BB${b.id} {\n  label="BB${b.id}";\n`)
            for (const i of b.insts) {
                const inps_label = i.inputs.map((_: Inst, idx: number) => `<TD PORT="f${idx}">${i.inputsNames === undefined ? '_' : i.inputsNames[idx]}</TD>`).join('')
                builder.push(`  inst_${i.id}[label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0"><TR><TD PORT="res">${i.op}</TD>${inps_label}</TR></TABLE>>];\n`);
            }
            for (let i = 1; i < b.insts.length; i++) {
                builder.push(`inst_${b.insts[i - 1].id} -> inst_${b.insts[i].id} [style=invis];`);
            }
            builder.push('\n}\n')
            for (const i of b.insts) {
                let idx = 0
                for (const inp of i.inputs) {
                    builder.push(`inst_${inp.id}:res:s -> inst_${i.id}:f${idx}:n;\n`);
                    idx++;
                }
            }
        }
        builder.push('}')

        for (const from of this.blocks) {
            if (from.insts.length == 1 && from.insts[0].op == '__entry') {
                from.insts = []
            }
        }

        return builder.join('')
    }
}

export class GraphState {
    breakTo: BBlock | undefined
    continueTo: BBlock | undefined
    names: Map<string, string> = new Map()

    clone(): GraphState {
        const r = new GraphState()
        r.breakTo = this.breakTo
        r.continueTo = this.continueTo
        r.names = new Map(this.names)
        return r
    }
}

export function convertFunctionToGraph(fn: ts.FunctionDeclaration): {g: Graph, allNames: Set<string>} {
    const g = new Graph();
    let cur_bb = g.entry;
    let cur_state = new GraphState()
    let allNames = new Set<string>()
    let nex_name = 0
    const registerVar = (name: string): string => {
        const new_name = `${name}\$${nex_name++}`;
        cur_state.names.set(name, new_name);
        allNames.add(new_name)
        return new_name
    }

    const scoped = <T>(x: () => T): T => {
        const old = cur_state
        const nevv = old.clone()
        cur_state = nevv
        const ret = x()
        cur_state = old
        return ret
    }

    for (const p of fn.parameters) {
        assert(p.name.kind == ts.SyntaxKind.Identifier);
        const name = registerVar((p.name as ts.Identifier).text)
        const par = cur_bb.inst(`parameter_${name}`)
        const id = cur_bb.inst(`set_${name}`)
        id.addInput(par)
    }

    const traverse = (n: ts.Node): Inst | undefined => {
        switch (n.kind) {
        case ts.SyntaxKind.Block: {
            scoped(() => {
                const bb = g.bb();
                cur_bb.addSucc(bb);
                cur_bb = bb;
                for (const i of (n as ts.Block).statements) {
                    traverse(i)
                }
            })
            return undefined;
        }
        case ts.SyntaxKind.Identifier: {
            const l = n as ts.Identifier
            return cur_bb.inst(`id_${cur_state.names.get(l.text)!}`)
        }
        case ts.SyntaxKind.NumericLiteral: {
            const l = n as ts.NumericLiteral
            return cur_bb.inst(`lit_${l.text}`)
        }
        case ts.SyntaxKind.IfStatement: {
            const c = n as ts.IfStatement
            const rs = traverse(c.expression)!
            const term = cur_bb.inst("jfalse");
            term.addInput(rs)
            const bbThen = g.bb();
            const bbEnd = g.bb();
            let bbElse = (c.elseStatement !== undefined) ? g.bb() : bbEnd;
            cur_bb.addSucc(bbElse, bbThen)
            cur_bb = bbThen
            traverse(c.thenStatement)
            if (cur_bb.succs.length == 0) {
                cur_bb.addSucc(bbEnd)
            }
            if (c.elseStatement !== undefined) {
                cur_bb = bbElse;
                traverse(c.elseStatement);
                cur_bb.addSucc(bbEnd);
            }
            cur_bb = bbEnd
            return undefined
        }
        case ts.SyntaxKind.CallExpression: {
            const c = n as ts.CallExpression
            assert(c.expression.kind == ts.SyntaxKind.Identifier)
            const args = c.arguments.map((a) => traverse(a)!)
            const call = cur_bb.inst(`call ${(c.expression as ts.Identifier).text}`)
            call.addInput(...args)
            return call
        }
        case ts.SyntaxKind.ExpressionStatement: {
            traverse((n as ts.ExpressionStatement).expression);
            return undefined;
        }
        case ts.SyntaxKind.ReturnStatement: {
            const rs = n as ts.ReturnStatement
            let rt: Inst | undefined = undefined
            if (rs.expression) {
                rt = traverse(rs.expression)!
            }
            const ins = cur_bb.inst('return')
            if (rt !== undefined) {
                ins.addInput(rt)
            }
            return undefined
        }
        case ts.SyntaxKind.BinaryExpression: {
            const bop = n as ts.BinaryExpression
            const bopTxt = bop.operatorToken.getText()
            if (bopTxt == '=') {
                assert(bop.left.kind == ts.SyntaxKind.Identifier);
                const r = traverse(bop.right)!
                const inst = cur_bb.inst(`set_${cur_state.names.get((bop.left as ts.Identifier).text)!}`)
                inst.addInput(r)
                return r
            } else {
                const l = traverse(bop.left)!;
                const r = traverse(bop.right)!;
                const ret = cur_bb.inst(bopTxt.replace('<', '&lt;'));
                ret.addInput(l, r)
                return ret
            }
        }
        case ts.SyntaxKind.WhileStatement: {
            const w = n as ts.WhileStatement
            const cond = g.bb()
            const body = g.bb()
            const end = g.bb()
            cur_bb.addSucc(cond)

            cur_bb = cond
            const condInst = traverse(w.expression)!
            cur_bb.inst("jfalse").addInput(condInst)
            cur_bb.addSucc(end, body)

            scoped(() => {
                cur_bb = body
                cur_state.breakTo = end
                cur_state.continueTo = cond
                traverse(w.statement)
                if (cur_bb.succs.length == 0) {
                    cur_bb.addSucc(cond)
                }
            })

            cur_bb = end
            return undefined
        }
        case ts.SyntaxKind.ForStatement: {
            const f = n as ts.ForStatement

            scoped(() => {
                if (f.initializer !== undefined) {
                    traverse(f.initializer)
                }

                const condBB = g.bb()
                const bodyBB = g.bb()
                const incBB = g.bb()
                const endBB = g.bb()

                cur_bb.addSucc(condBB)
                cur_bb = condBB
                if (f.condition !== undefined) {
                    const j = traverse(f.condition)!
                    const jf = cur_bb.inst("jfalse")
                    jf.addInput(j)
                    cur_bb.addSucc(endBB, bodyBB)
                } else {
                    cur_bb.addSucc(bodyBB)
                }

                scoped(() => {
                    cur_state.breakTo = endBB
                    cur_state.continueTo = incBB
                    cur_bb = bodyBB
                    traverse(f.statement)
                    cur_bb.addSucc(incBB)
                })

                cur_bb = incBB
                if (f.incrementor !== undefined) {
                    traverse(f.incrementor)
                }
                cur_bb.addSucc(condBB)

                cur_bb = endBB
            })

            return undefined
        }
        case ts.SyntaxKind.VariableDeclarationList: {
            const vl = n as ts.VariableDeclarationList
            assert(vl.declarations.length == 1)
            traverse(vl.declarations[0])
            return undefined
        }
        case ts.SyntaxKind.VariableDeclaration: {
            const v = n as ts.VariableDeclaration
            const init = traverse(v.initializer!)!
            const id = cur_bb.inst(`set_${registerVar((v.name as ts.Identifier).text)}`)
            id.addInput(init)
            return undefined
        }
        case ts.SyntaxKind.BreakStatement: {
            cur_bb.addSucc(cur_state.breakTo!)
            return undefined
        }
        case ts.SyntaxKind.ContinueStatement: {
            cur_bb.addSucc(cur_state.continueTo!)
            return undefined
        }
        case ts.SyntaxKind.VariableStatement: {
            const vl = n as ts.VariableStatement
            assert(vl.declarationList.declarations.length == 1);
            return traverse(vl.declarationList.declarations[0]);
        }
        default:
            console.log(n);
            throw new Error("unknown kind " + n.kind);
        }
        assert(false)
    };
    traverse(fn.body!);
    return {g, allNames};
}

export function graphToSSA(g: Graph, allNames: Set<string>): void {
    const visited = new Set<BBlock>()
    const data = new Map<BBlock, Map<string, Inst>>()

    // bfs to insert phi's
    const queue: BBlock[] = [g.entry]
    for (let i = 0; i < queue.length; i++) {
        const b = queue[i]
        if (visited.has(b)) {
            continue
        }
        if (b.preds.length == 1) {
            assert(visited.has(b.preds[0]))
            data.set(b, new Map(data.get(b.preds[0])))
        } else if (b.preds.length == 0) {
            data.set(b, new Map())
        } else {
            const ans = new Map()
            data.set(b, ans)
            for (const varName of allNames) {
                let different = false
                let inst: Inst | undefined = undefined
                for (const pred of b.preds) {
                    if (!visited.has(pred)) {
                        different = true
                        break
                    }
                    const oldData = data.get(pred)!
                    const res = oldData.get(varName)
                    if (res !== undefined) {
                        if (inst === undefined) {
                            inst = res
                        } else if (inst != res) {
                            different = true
                            break
                        }
                    }
                }
                if (different) {
                    const phi = b.phi(varName)
                    ans.set(varName, phi)
                } else if (inst !== undefined) {
                    ans.set(varName, inst!)
                }
            }
        }
        // calculate updates and patch instructions removing identifiers
        const ans = data.get(b)!
        for (let i = 0; i < b.insts.length; i++) {
            const inst = b.insts[i]
            if (inst.op.startsWith("id_")) {
                const name = inst.op.substring(3)
                const prevInst = ans.get(name)
                assert(prevInst !== undefined, `undefined var ${name}`)
                inst.replaceUsers(prevInst)
                b.insts.splice(i, 1)
                i--
            } else if (inst.op.startsWith("set_")) {
                const name = inst.op.substring(4)
                ans.set(name, inst.inputs[0])
                b.insts.splice(i, 1)
                i--
            }
        }
        visited.add(b)
        for (const n of b.succs) {
            if (!visited.has(n)) {
                queue.push(n)
            }
        }
    }
    // set phi inputs
    for (let b of g.blocks) {
        for (let i of b.insts) {
            if (!i.op.startsWith("phi_")) {
                continue;
            }
            const name = i.op.substring(4)
            i.addInput(...b.preds.map(p => data.get(p)!.get(name)!))
            i.inputsNames = b.preds.map(p => `${p.id}`)
        }
    }
}

export function eliminateEmptyBB(g: Graph): void {
    let was = true
    while (was) {
        was = false
        for (let i = 0; i < g.blocks.length; i++) {
            const b = g.blocks[i]
            if (b.insts.length == 0 && b.preds.length == 1 && b.succs.length == 1) {
                was = true
                const n = b.succs[0]
                const p = b.preds[0]
                b.preds.forEach((pb) => pb.succs = pb.succs.map((s) => s == b ? n : s))
                b.succs.forEach((pb) => pb.preds = pb.preds.map((s) => s == b ? p : s))
                b.succs.forEach(pb => pb.insts.forEach(nxtInst => {
                    if (!nxtInst.op.startsWith('phi_')) {
                        return
                    }
                    nxtInst.inputsNames = nxtInst.inputsNames!.map(o => o == `${b.id}` ? `${p.id}` : o)
                }));
                b.preds = []
                b.succs = []
                g.blocks.splice(i, 1)
                i--
            }
        }
    }
}

export function eliminatePhi(g: Graph): void {
    for (let b of g.blocks) {
        for (let i = 0 ; i < b.insts.length; i++) {
            const phi = b.insts[i]
            if (!phi.op.startsWith("phi_")) {
                continue;
            }
            let remove = true
            let inp: Inst | undefined = undefined
            for (const i of phi.inputs) {
                if (inp === undefined) {
                    inp = i
                } else if (i != phi && i != inp) {
                    remove = false;
                    break
                }
            }
            remove = remove || (phi.users.length == 0)
            if (remove) {
                phi.inputs.forEach(inp => inp.users = inp.users .filter(u => u != phi).concat(phi.users))
                phi.users.forEach(us => us.inputs = us.inputs.map(x => x == phi ? inp! : x))
                b.insts.splice(i, 1)
                i--
            }
        }
    }
}
