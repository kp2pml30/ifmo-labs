import * as ts from 'typescript'

type Input = Inst | string

export function assert(b: boolean, msg?: string) {
    if (!b) {
        throw new Error('assertion failed ' + msg)
    }
}

export class Inst {
    bb: BBlock
    id: number
    op: string
    name: string | undefined
    inputs: Input[] = []
    inputsNames: string[] | undefined = undefined
    users: Inst[] = []
    dumpAlways = false
    saveToVar = false
    returns = true

    getName(): string {
        if (this.name !== undefined) {
            return this.name
        }
        return `v${this.id}`
    }

    getNameSet(): string {
        if (!this.returns) {
            assert(this.users.length == 0)
            assert(this.name === undefined)
            return this.op
        }
        if (this.name !== undefined) {
            return `${this.name} = ${this.op}`
        }
        return `v${this.id} = ${this.op}`
    }

    constructor(bb: BBlock, id: number, op: string) {
        this.bb = bb
        this.id = id
        this.op = op
    }

    addInput(...inp: Input[]): void {
        this.inputs.push(...inp)
        for (const i of inp) {
            if (i instanceof Inst) {
                i.users.push(this)
            }
        }
    }

    replaceUsers(w: Inst): void {
        w.users.push(...this.users)
        for (const u of this.users) {
            u.inputs = u.inputs.map((x) => x == this ? w : x)
        }
    }

    trivial(): string | Inst {
        if (this.saveToVar) {
            return this
        }
        if (this.name !== undefined) {
            return this.name
        }
        if (this.inputs.every(x => x instanceof Inst ? (typeof x.trivial() == 'string') : true)) {
            return `(${this.op} ${this.inputs.map(x => x instanceof Inst ? x.trivial() : x).join(', ')})`
        }
        return this
    }
}

function dumpTrivial(t: string | Inst): string {
    if (t instanceof Inst) {
        return t.getName()
    }
    return t
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
        r.name = `${name}.${r.id}`
        r.dumpAlways = true
        return r
    }

    setSuccs(...bbs: BBlock[]) {
        assert(!this.terminated)
        this.terminated = true
        this.succs.push(...bbs)
        for (const b of bbs) {
            b.preds.push(this)
        }
    }

    insts: Inst[] = []
    succs: BBlock[] = []
    preds: BBlock[] = []
    terminated = false
}

function inputToString(i: Input): string {
    if (i instanceof Inst) {
        return dumpTrivial(i.trivial())
    }
    return i
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
        const blockInsts = new Map(this.blocks.map(b => [b, b.insts.filter(i => i.dumpAlways || typeof i.trivial() != 'string')]))
        for (const [from, insts] of blockInsts.entries()) {
            if (insts.length == 0) {
                const i = from.inst('__empty_bb')
                i.returns = false
                i.dumpAlways = true
                insts.push(i)
            }
        }
        for (const from of this.blocks) {
            let succ_id = 0
            const colors = new Map<number, string>([[0, 'red'], [1, 'green']])
            for (const to of from.succs) {
                const f = blockInsts.get(from)!.at(-1)!
                const t = blockInsts.get(to)![0]
                // ltail=cluster_BB${from.id}, lhead=cluster_BB${to.id},
                builder.push(`inst_${f.id}:res:s -> inst_${t.id}:res:n [color=${colors.get(succ_id)}];`)
                succ_id += 1
            }
        }
        builder.push("\n\n")
        for (const b of this.blocks) {
            const bInsts = blockInsts.get(b)!
            builder.push(`subgraph cluster_BB${b.id} {\n  label="BB${b.id}";\n`)
            for (const i of bInsts) {
                const inps_label = i.inputs.map((_: Input, idx: number) => `<TD PORT="f${idx}">${i.inputsNames === undefined ? '' : `${i.inputsNames[idx]} ;; `}${inputToString(i.inputs[idx])}</TD>`).join('')
                builder.push(`  inst_${i.id}[label=<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0"><TR><TD PORT="res">${i.getNameSet()}</TD>${inps_label}</TR></TABLE>>];\n`);
            }
            for (let i = 1; i < bInsts.length; i++) {
                builder.push(`inst_${bInsts[i - 1].id} -> inst_${bInsts[i].id};`);
            }
            builder.push('\n}\n')
        }
        builder.push('}')

        for (const from of this.blocks) {
            from.insts = from.insts.filter(i => i.op != '__empty_bb')
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
        id.dumpAlways = true
        id.addInput(par)
    }

    const traverse = (n: ts.Node): Input | undefined => {
        switch (n.kind) {
        case ts.SyntaxKind.Block: {
            scoped(() => {
                const bb = g.bb();
                cur_bb.setSuccs(bb);
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
            return `${l.text}`
        }
        case ts.SyntaxKind.IfStatement: {
            const c = n as ts.IfStatement
            const rs = traverse(c.expression)!
            const term = cur_bb.inst("jfalse");
            term.returns = false
            term.addInput(rs)
            const bbThen = g.bb();
            const bbEnd = g.bb();
            let bbElse = (c.elseStatement !== undefined) ? g.bb() : bbEnd;
            cur_bb.setSuccs(bbElse, bbThen)
            cur_bb = bbThen
            traverse(c.thenStatement)
            if (!cur_bb.terminated) {
                cur_bb.setSuccs(bbEnd)
            }
            if (c.elseStatement !== undefined) {
                cur_bb = bbElse;
                traverse(c.elseStatement);
                cur_bb.setSuccs(bbEnd);
            }
            cur_bb = bbEnd
            return undefined
        }
        case ts.SyntaxKind.ParenthesizedExpression: {
            return traverse((n as ts.ParenthesizedExpression).expression)
        }
        case ts.SyntaxKind.CallExpression: {
            const c = n as ts.CallExpression
            assert(c.expression.kind == ts.SyntaxKind.Identifier)
            const args = c.arguments.map((a) => traverse(a)!)
            const call = cur_bb.inst(`call ${(c.expression as ts.Identifier).text}`)
            call.dumpAlways = true
            call.saveToVar = true
            call.addInput(...args)
            return call
        }
        case ts.SyntaxKind.ExpressionStatement: {
            traverse((n as ts.ExpressionStatement).expression);
            return undefined;
        }
        case ts.SyntaxKind.ReturnStatement: {
            const rs = n as ts.ReturnStatement
            let rt: Input | undefined = undefined
            if (rs.expression) {
                rt = traverse(rs.expression)!
            }
            const ins = cur_bb.inst('return')
            ins.dumpAlways = true
            ins.returns = false
            if (rt !== undefined) {
                ins.addInput(rt)
            }
            cur_bb.setSuccs()
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
                inst.dumpAlways = true
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
            cur_bb.setSuccs(cond)

            cur_bb = cond
            const condInst = traverse(w.expression)!
            const term = cur_bb.inst("jfalse")
            term.addInput(condInst)
            term.returns = false
            cur_bb.setSuccs(end, body)

            scoped(() => {
                cur_bb = body
                cur_state.breakTo = end
                cur_state.continueTo = cond
                traverse(w.statement)
                if (!cur_bb.terminated) {
                    cur_bb.setSuccs(cond)
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

                cur_bb.setSuccs(condBB)
                cur_bb = condBB
                if (f.condition !== undefined) {
                    const j = traverse(f.condition)!
                    const jf = cur_bb.inst("jfalse")
                    jf.addInput(j)
                    jf.returns = false
                    cur_bb.setSuccs(endBB, bodyBB)
                } else {
                    cur_bb.setSuccs(bodyBB)
                }

                scoped(() => {
                    cur_state.breakTo = endBB
                    cur_state.continueTo = incBB
                    cur_bb = bodyBB
                    traverse(f.statement)
                    cur_bb.setSuccs(incBB)
                })

                cur_bb = incBB
                if (f.incrementor !== undefined) {
                    traverse(f.incrementor)
                }
                cur_bb.setSuccs(condBB)

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
            id.dumpAlways = true
            id.addInput(init)
            return undefined
        }
        case ts.SyntaxKind.BreakStatement: {
            cur_bb.setSuccs(cur_state.breakTo!)
            cur_bb = g.bb()
            return undefined
        }
        case ts.SyntaxKind.ContinueStatement: {
            cur_bb.setSuccs(cur_state.continueTo!)
            const old = cur_bb
            cur_bb = g.bb()
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
                inst.replaceUsers(prevInst!)
                b.insts.splice(i, 1)
                i--
            } else if (inst.op.startsWith("set_")) {
                const name = inst.op.substring(4)
                const ini = inst.inputs[0]
                if (ini instanceof Inst) {
                    if (ini.name !== undefined) {
                        ans.set(name, ini)
                        b.insts.splice(i, 1)
                        i--
                        continue
                    }
                }
                inst.name = `${name}.${inst.id}`
                inst.dumpAlways = true
                ans.set(name, inst)
                inst.op = ''
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
    const visited = new Set<BBlock>()
    const dfs = (x: BBlock) => {
        if (visited.has(x)) {
            return
        }
        visited.add(x)
        x.succs.forEach(dfs)
    }
    dfs(g.entry)
    g.blocks = g.blocks.filter(y => visited.has(y))
    g.blocks.forEach(b => b.preds = b.preds.filter(y => visited.has(y)))

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
            let inp: Input | undefined = undefined
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
                phi.inputs.forEach(inp => { if (inp instanceof Inst) inp.users = inp.users.filter(u => u != phi).concat(phi.users) })
                phi.users.forEach(us => us.inputs = us.inputs.map(x => x == phi ? inp! : x))
                b.insts.splice(i, 1)
                i--
            }
        }
    }
}
