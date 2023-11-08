function main(a: boolean): number {
    let x = 11;
    let y = x + 10;
    let y = x + 12;
    if (a) {
        x = x + 2;
    } else {
        x = x - 11;
    }
    f(x, y)

    let z = 30

    for (let i = 0; i < 10; i = i + 1) {
        print(z)
        y = f(y)
        if (y == 1) {
            break;
        }
        if (y == 12) {
            continue
        }
        y = f(y)
    }
    return x + y
}
