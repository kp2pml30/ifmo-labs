import {describe, expect, test, beforeEach, afterEach, jest } from '@jest/globals';
import * as jestG from '@jest/globals';

import { strict as assert } from 'node:assert'
import { GenericContainer, StartedTestContainer } from 'testcontainers'
import * as data from './data';
import fetch from 'node-fetch'
import {UserManager} from './users'

let container: StartedTestContainer | undefined = undefined

jest.setTimeout(10000)

beforeEach(async () => {
	container = await new GenericContainer('kp2pml30/testcontainers-hw')
		.withExposedPorts(8080)
		.start()
})

afterEach(async () => {
	await container?.stop();
})

function exchangeURL() {
	return new URL(`http://${container!.getHost()}:${container!.getMappedPort(8080)}`)
}

function composeURL(p: string, opts: any): URL {
	//console.log(u)
	const url = exchangeURL()
	url.pathname = p;
	for (const p in opts) {
		url.searchParams.set(p, opts[p])
	}
	return url
}

async function newExchange(um: UserManager, p: data.ExchangeNew) {
	await um.makeRequest('exchange/new', p)
}

test('new exchange', async () => {
	const um = new UserManager(exchangeURL())
	await newExchange(um, {id: '1'})

	await expect(newExchange(um, {id: '1'})).rejects.toThrow()
})

async function initExchange(um: UserManager, id: string, count: number, price: number) {
	await expect(
		um.makeRequest('exchange/setPrice', {id: id, newPrice: `${price}`} satisfies data.ExchangeSetPrice)
	).resolves.not.toThrow()

	await expect(
		um.makeRequest('exchange/addStocks', {id: id, addCount: `${count}`} satisfies data.ExchangeAddStocks)
	).resolves.not.toThrow()
}

async function allStats(): Promise<number> {
	const b = await fetch(composeURL('stats/all', {}))
	expect(b.status).toEqual(200)
	const bj = await b.json()
	return bj.sum
}

test('stats', async () => {
	const um = new UserManager(exchangeURL())

	await newExchange(um, {id: '1'})
	await newExchange(um, {id: '2'})

	expect(await allStats()).toEqual(0)

	await initExchange(um, '1', 1, 20)
	await initExchange(um, '2', 3, 40)
	expect(await allStats()).toEqual(20 + 3*40)
})

test('users', async () => {
	const um = new UserManager(exchangeURL())
	await newExchange(um, {id: '1'})
	await initExchange(um, '1', 3, 10)

	const u1 = um.newUser()
	await expect(u1.buy('1', 9, 0.5)).rejects.toThrow()
	await expect(u1.buy('1', 9, 2)).rejects.toThrow()
	u1.replenish(11)
	await expect(u1.buy('1', 9, 2)).resolves.not.toThrow()

	await um.updateStats()
	expect(u1.stats()).toEqual(1 + 10)

	await expect(
		um.makeRequest('exchange/setPrice', {id: '1', newPrice: '100'} satisfies data.ExchangeSetPrice)
	).resolves.not.toThrow()

	expect(u1.stats()).toEqual(1 + 10)
	await um.updateStats()
	expect(u1.stats()).toEqual(1 + 100)

	await expect(
		um.makeRequest('exchange/setPrice', {id: '1', newPrice: '2'} satisfies data.ExchangeSetPrice)
	).resolves.not.toThrow()

	await expect(u1.sell('1', 3)).rejects.toThrow()

	await expect(u1.sell('1', 1)).resolves.not.toThrow()
	await expect(
		um.makeRequest('exchange/setPrice', {id: '1', newPrice: '40'} satisfies data.ExchangeSetPrice)
	).resolves.not.toThrow()
	await um.updateStats()
	expect(u1.stats()).toEqual(1 + 2) // anti stonks
})
