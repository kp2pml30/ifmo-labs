export interface ExchangeNew {
	id: string
}

export interface ExchangeSetPrice {
	id: string,
	newPrice: string
}

export interface ExchangeAddStocks {
	id: string,
	addCount: string
}

export interface ExchangeBuy {
	id: string,
	balance: string,
	expectedPrice: string,
	epsilon: string
}

export interface ExchangeSell {
	id: string,
	minPrice: string,
}

export type Stock = {count: number, price: number}
export type Exchange = Map<string, Stock>
