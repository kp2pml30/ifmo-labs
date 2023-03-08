import { strict as assert } from 'node:assert'
import fetch from 'node-fetch'
import * as data from './data';

export interface User {
	id: string
	balance: number
	stocks: Map<string, number>
}

export class LocalUser {
	private manager: UserManager
	id: string
	balance: number
	stocks: Map<string, number>

	constructor(manager: UserManager, id: string) {
		this.manager = manager
		this.id = id
		this.balance = 0
		this.stocks = new Map()
	}

	replenish(addAmount: number) {
		assert(addAmount >= 0)
		this.balance += addAmount
	}

	// actually, I do not understand how to avoid 2 generals problem
	// and how users can be managed not by exchange
	// hope it doesn't affect this hw too much
	// isn't it like exchange has account for some sub-exchange,
	//   which stores users and is an exchange-user, whose balance and stocks
	//   are sum of users belongings?
	async buy(id: string, price: number, epsilon: number) {
		const a = await this.manager.makeRequest('exchange/buy', {id, expectedPrice: `${price}`, epsilon: `${epsilon}`, balance: `${this.balance}`} satisfies data.ExchangeBuy)
		this.balance -= a.actualPrice
		this.stocks.set(id, (this.stocks.get(id) ?? 0) + 1)
	}

	async sell(id: string, minPrice: number) {
		const old = this.stocks.get(id) ?? 0
		assert(old > 0)
		const a = await this.manager.makeRequest('exchange/sell', {id, minPrice: `${minPrice}`} satisfies data.ExchangeSell)
		this.balance += a.actualPrice
		this.stocks.set(id, old - 1)
	}

	stats(): number {
		const s = this.manager.stats ?? new Map() as data.Exchange
		let sum = this.balance
		for (const o of this.stocks) {
			sum += o[1] * (s.get(o[0])?.price ?? 0)
		}
		return sum
	}
}

class UMRequestError extends Error {
	data: any

	constructor(data: any) {
		super('UMRequestError')
		this.data = data
	}

	public toString(): string {
		return `UMRequestError: ${JSON.stringify(this.data)}`
	}
}

export class UserManager {
	nextId: number = 0
	exchangeUrl: URL
	stats: data.Exchange | undefined

	constructor(exchangeUrl: URL) {
		this.exchangeUrl = exchangeUrl
	}

	async updateStats() {
		this.stats = new Map(Object.entries((await this.makeRequest('stats/all', {})).exchange))
	}

	newUser(): LocalUser {
		return new LocalUser(this, `${this.nextId++}`)
	}

	async makeRequest(p: string, opts: any): Promise<any> {
		const u = new URL(this.exchangeUrl)
		u.pathname = p
		for (const p in opts) {
			u.searchParams.set(p, opts[p])
		}
		const a = await fetch(u)
		const js = await a.json()
		//console.log(p, opts, a.status, js)
		if (a.status != 200) {
			throw new UMRequestError(js)
		}
		return js;
	}
}
