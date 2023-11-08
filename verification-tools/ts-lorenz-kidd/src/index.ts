import * as ts from 'typescript'
import {readFile, writeFile} from 'fs/promises';
import * as i from './impl'

import assert from 'assert'

(async function() {
    const fName = process.argv.at(-2)!
    const out = process.argv.at(-1)!

    const save = async function(x: any) {
        await writeFile(`${out}`, `${x}\n`)
    }

    const fle = (await readFile(fName)).toString()
    const program = i.programFromText(fle);
    const res = i.analyze(program)

    await save(JSON.stringify(res, undefined, "  "));

    const dumpMetric = (name: string, metric: i.FinalMetric) => {
        console.log(`  ${metric.ok ? '✓' : '✗'} ${name} = ${Math.round(metric.value * 100) / 100}\t| ${metric.fullName} # ${metric.reason}`)
    }

    const traverseMetricsIn = <T>(inp: { [key: string]: T }, updater: (x: T) => { [key: string]: i.FinalMetric }) => {
        for (const name in inp) {
            const val = inp[name]
            console.log(name)
            const upd = updater(val)
            for (const metric in upd) {
                dumpMetric(metric, upd[metric])
            }
        }
    }

    console.log('CLASSES')
    traverseMetricsIn(res.classMetricsData, i.calcClassMetrics)
    console.log('METHODS')
    traverseMetricsIn(res.methodMetricsData, i.calcMethodMetrics)
    console.log('PROJECT')
    const nkc = res.projectMetricsData.keyClasses / res.projectMetricsData.classesCount
    dumpMetric("nkc", { fullName: "number of key classes", value: nkc, ok: 0.2 <= nkc && nkc <= 0.4, reason: "0.2 <= nkc <= 0.4" })
})()
