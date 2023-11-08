function main(): void {
    let x = 11
    let y = 12
    if (f()) {
        x = x + 10
    } else {
        x = (x - 11) * y
    }
    g(x, y)
}
