export type Currency = {id: number, sign: string, coef: number}

export const currencies: Currency[] = [
	{
		id: 1,
		sign: '$',
		coef: 1
	},
	{
		id: 2,
		sign: '€',
		coef: 2
	}
]
