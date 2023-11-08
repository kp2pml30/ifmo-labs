import * as i from './impl'

export function runOn(text: string, to: HTMLDivElement): void {
    to.innerHTML = ""
    const program = i.programFromText(text);
    const res = i.analyze(program)

    console.log(JSON.stringify(res, undefined, "  "));
    const txt = []

    txt.push(`<h1>classes</h1>`)
    txt.push("<ul>")
    for (const className in res.classMetricsData) {
        txt.push(`<li>${className}`)
        const met = i.calcClassMetrics(res.classMetricsData[className]);
        txt.push("<ul>")
        for (const metName in met) {
            const metVal = met[metName]
            txt.push(`<li>${metName} (${metVal.fullName}) = ${metVal.value}${metVal.ok && metVal.failCause ? ' failed due to `' + metVal.failCause + "`" : ''}</li>`)
        }
        txt.push("</ul>")
        txt.push(`</li>`)
    }
    txt.push("</ul>")
    to.innerHTML = txt.join('')
}

(window as any)['runOn'] = runOn
