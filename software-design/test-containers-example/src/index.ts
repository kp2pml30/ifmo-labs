import * as util from 'util';

import * as querystring from 'node:querystring';

import { stdin as input, stdout as output } from 'node:process';
import { resolve } from 'node:path';
import { assert as isAs } from 'typia';
import {strict as assert} from 'node:assert'

import * as http from 'http';

import * as data from './data';

let port = Number.parseInt(process.argv[4]);
if (Number.isNaN(port)) {
	port = 8080
}

console.log(`selected port ${port}`)

const exchange: data.Exchange = new Map<string, data.Stock>()

interface BadAnswer {
	status: string
	[key: string]: any
}

interface OkAnswer {
	status: 'ok'
	[key: string]: any
}

const server = http.createServer((req, res) => {
	const url = new URL('http://127.0.0.1' + req.url!);
	const params = Object.fromEntries(url.searchParams.entries()) as any;
	const path = url.pathname.replace(/^\/*/, '');
	const answerWith = (o: OkAnswer) => {
		res.statusCode = 200
		res.setHeader('Content-Type', 'application/json')
		res.end(JSON.stringify(o))
	}
	const badAnswer = (s: BadAnswer) => {
		console.log(s, typeof s)
		res.statusCode = 400
		res.setHeader('Content-Type', 'application/json')
		res.end(JSON.stringify(s))
	}
	try {
		switch (path) {
		case 'exchange/new': {
			const p = isAs<data.ExchangeNew>(params)
			console.log(p)
			if (exchange.has(p.id)) {
				badAnswer({status: "exists"})
				break
			}
			exchange.set(p.id, {count: 0, price: Infinity})
			answerWith({status: "ok"})
			break;
		}
		case 'exchange/setPrice': {
			const p = isAs<data.ExchangeSetPrice>(params)
			const old = exchange.get(p.id)
			if (old === undefined) {
				badAnswer({status: "not found"})
				break
			}
			old!.price = Number.parseFloat(p.newPrice)
			answerWith({status: "ok"})
			break;
		}
		case 'exchange/addStocks': {
			const p = isAs<data.ExchangeAddStocks>(params)
			const old = exchange.get(p.id)
			if (old === undefined) {
				badAnswer({status: "not found"})
				break
			}
			old.count += Number.parseFloat(p.addCount)
			answerWith({status: "ok", "newCount": old.count})
			break;
		}
		case 'exchange/buy': {
			const p = isAs<data.ExchangeBuy>(params)
			const old = exchange.get(p.id)
			if (old === undefined) {
				badAnswer({status: "not found"})
				break
			}
			const cou = 1
			if (old.count < cou) {
				badAnswer({status: "no-stocks"})
				break
			}
			const balance = Number.parseFloat(p.balance)
			assert(!Number.isNaN(balance))
			if (Math.abs(old.price - Number.parseFloat(p.expectedPrice)) > Number.parseFloat(p.expectedPrice)) {
				badAnswer({status: "price-exceeds", "newPrice": old.price})
				break
			}
			if (old.price > balance) {
				badAnswer({status: "no-money", "newPrice": old.price})
				break
			}
			old.count -= cou
			answerWith({status: "ok", "actualPrice": old.price})
			break
		}
		case 'exchange/sell': {
			const p = isAs<data.ExchangeSell>(params)
			const old = exchange.get(p.id)
			if (old === undefined) {
				badAnswer({status: "not found"})
				break
			}
			const cou = 1
			const minP = Number.parseFloat(p.minPrice)
			assert(!Number.isNaN(minP))
			if (old.price < minP) {
				badAnswer({status: "price-below", "newPrice": old.price})
				break
			}
			old.count += cou
			answerWith({status: "ok", "actualPrice": old.price})
			break
		}
		case 'stats/all': {
			let sum = 0
			for (const p of exchange) {
				if (p[1].count != 0) { // infinity * 0 = nan
					sum += p[1].count * p[1].price
				}
			}
			answerWith({"status": "ok", sum, exchange: Object.fromEntries(exchange)})
			break
		}
		default:
			badAnswer({status: 'unknown command', command: path})
		}
	} catch (e: any) {
		badAnswer({status: 'exception', exception: e})
	}
});

const hostname = '0.0.0.0'

server.listen(port, hostname, () => {
	console.log(`Server running at http://${hostname}:${port}/`);
});
