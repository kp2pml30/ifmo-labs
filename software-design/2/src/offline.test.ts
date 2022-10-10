import {describe, expect, test} from '@jest/globals';
import {jest} from '@jest/globals';
import {mocked} from 'jest-mock'
import fetch from 'node-fetch';
import * as http from 'http';

import * as i from './index';

import { strict as assert } from 'node:assert';

const fakeNow = new Date('2020-01-01')

function getBeforeHours(hours: number): Date {
	const d = new Date(fakeNow)
	d.setHours(fakeNow.getHours()-hours)
	return d
}

jest
	.useFakeTimers()
	.setSystemTime(fakeNow)
jest.mock('node-fetch')

test('testing works', () => {
	expect(1).toBe(1)
})

class ResultsType {
	forNull: i.ThreadListResponse | undefined
	entries: Map<string, i.ThreadListResponse>

	constructor(forNull: i.ThreadListResponse | undefined, entries: Map<string, i.ThreadListResponse>) {
		this.forNull = forNull
		this.entries = entries
	}

	get(key: null | string): undefined | i.ThreadListResponse {
		if (key === null) {
			return this.forNull
		} else {
			return this.entries.get(key)
		}
	}

	set(key: null | string, value: i.ThreadListResponse) {
		if (key === null) {
			this.forNull = value
		} else {
			this.entries.set(key, value)
		}
	}

	has(key: null | string): boolean {
		return this.get(key) !== undefined
	}
}

var nextPort = 0

class MockResponser {
	results: ResultsType
	getCounts = 0

	constructor(results: ResultsType) {
		assert.equal(results.has(null), true)
		this.results = results
	}

	fakeMock() {
		mocked(fetch).mockImplementation(((url0: URL | RequestInfo, init?: RequestInit | undefined): Promise<Response> => {
			const url = url0 as URL
			this.getCounts++
			const page = url.searchParams.get("pageToken")
			let res = this.results.get(page)
			if (res === undefined) {
				return Promise.resolve({
					status: 400,
					ok: false,
				} as unknown as Response)
			}
			return Promise.resolve({
				status: 200,
				ok: true,
				json: () => Promise.resolve(res)
			} as unknown as Response)
		}) as unknown as typeof fetch)
	}

	async fakeHttp(cb: (url: string) => Promise<void>) {
		const port = 30303 //+ nextPort++
		const fakeUrl = `http://127.0.0.1:${port}`

		const requestListener = (hreq: http.IncomingMessage, hres: http.ServerResponse) => {
			const url = new URL(hreq.url as string, fakeUrl)
			this.getCounts++
			const page = url.searchParams.get("pageToken")
			let res = this.results.get(page)
			if (res === undefined) {
				hres.writeHead(400)
				hres.end()
				return
			}
			hres.writeHead(200)
			hres.end(JSON.stringify(res))
		}
		const serv = http.createServer(requestListener)

		serv.listen(port)
		try {
			await cb(fakeUrl)
		} finally {
			await new Promise((resolve, reject) => {
				serv.close((err: Error | undefined) => {
					if (err === undefined) {
						resolve(null)
					} else {
						reject(err)
					}
				})
			})
		}
	}

	async get(url: URL): Promise<i.BadResult | unknown> {
		this.getCounts++
		const page = url.searchParams.get("pageToken")
		let res = this.results.get(page)
		if (res === undefined) {
			return {
				kind: "bad",
				statusCode: 400
			}
		}
		return {
			kind: "ok",
			json: res
		}
	}
}

const mockVideoId = "videoId"
const mockChannelId = "channelId"
var idCounter = 0

interface ResponseBuilder {
	response(items: i.CommentThreadResource[]): ResponseBuilder
	finish(): ResultsType
}

class ThreadMaker {
	dates = Array<Date>()

	comment(published: Date): i.CommentResource {
		this.dates.push(published)
		return {
			id: (idCounter++).toString(),
			kind: "youtube#comment",
			snippet: {
				authorDisplayName: "name",
				authorProfileImageUrl: "https://",
				authorChannelUrl: "https://",
				authorChannelId: {
					value: "123"
				},
				channelId: "123",
				videoId: mockVideoId,
				textDisplay: "123",
				textOriginal: "123",
				parentId: "",
				canRate: true,
				viewerRating: "10",
				moderationStatus: "ok",
				likeCount: 0,
				publishedAt: published.toISOString(),
				updatedAt: published.toISOString()
			}
		}
	}

	thread(topLevel: i.CommentResource, replies: i.CommentResource[]): i.CommentThreadResource {
		return {
			kind: "youtube#commentThread",
			id: (idCounter++).toString(),
			snippet: {
				channelId: mockChannelId,
				videoId: mockVideoId,
				topLevelComment: topLevel,
				canReply: replies.length > 0 ? true : false,
				totalReplyCount: replies.length,
				isPublic: true
			},
			replies: {
				comments: replies
			}
		}
	}

	response(nextPageToken: string | null, items: i.CommentThreadResource[]): i.ThreadListResponse {
		return {
			kind: "youtube#commentThreadListResponse",
			nextPageToken: nextPageToken,
			pageInfo: {
				"totalResults": 1e10,
				"resultsPerPage": items.length
			},
			items: items
		}
	}

	builder(items: i.CommentThreadResource[]): ResponseBuilder {
		const result = new ResultsType(undefined, new Map())
		var page0 = 0
		var prevPage = this.response(null, items)
		result.set(null, prevPage)
		let builder: ResponseBuilder = {
			finish: () => {
				return result
			},
			response: (items) => {
				const newId = (page0++).toString()
				prevPage.nextPageToken = newId
				prevPage = this.response(null, items)
				result.set(newId, prevPage)
				return builder
			},
		}
		return builder
	}

	getDates(hours: number): number[] {
		let res = new Array<number>(hours).fill(0)
		for (const d of this.dates) {
			const getDatesDiffHours = (a: Date, b: Date) => {
				// is there a better way?
				return (a.getTime() - b.getTime()) / 36e5
			}
			const diff = Math.floor(getDatesDiffHours(fakeNow, d))
			if (diff < res.length) {
				res[diff]++
			}
		}
		return res
	}
}

const noComments = Array<i.CommentResource>(0)

const originalFetch = jest.requireActual('node-fetch') as any

async function verifyWithHttp(m0: MockResponser, rp: ResultsType, oldGot: number[] | i.BadResult, hours: number) {
	mocked(fetch).mockImplementation(originalFetch)
	const m1 = new MockResponser(rp)
	await m1.fakeHttp( async (url: string) => {
		const got1 = await i.getCommentsStats(mockVideoId, hours, url)
		expect(m0.getCounts).toEqual(m1.getCounts)
		expect(got1).toEqual(oldGot)
	})
	jest.mock('node-fetch')
}

test('mock constructor fails on empty', () => {
	expect(() => {
		new MockResponser(new ResultsType(undefined, new Map())).fakeMock()
		i.getCommentsStats(mockVideoId, 10)
	}).toThrow()
})

test('empty page', async () => {
	const m = new ThreadMaker()
	const rp = m.builder([]).finish()
	const hours = 30
	const expected = m.getDates(hours)
	const m0 = new MockResponser(rp)
	m0.fakeMock()
	const got = await i.getCommentsStats(mockVideoId, hours)
	expect(got).toEqual(expected)

	await verifyWithHttp(m0, rp, got, hours)
})

test('one page', async () => {
	const m = new ThreadMaker()
	const rp = m.builder([
		m.thread(m.comment(getBeforeHours(1)), []),
		m.thread(m.comment(getBeforeHours(2)), []),
		m.thread(m.comment(getBeforeHours(3)), [])
	]).finish()
	const hours = 4
	const expected = m.getDates(hours)
	expect(expected).toEqual([0, 1, 1, 1])
	const m0 = new MockResponser(rp)
	m0.fakeMock()
	const got = await i.getCommentsStats(mockVideoId, hours)
	expect(got).toEqual(expected)

	await verifyWithHttp(m0, rp, got, hours)
})

test('two pages', async () => {
	const m = new ThreadMaker()
	const rp = m
		.builder([
			m.thread(m.comment(getBeforeHours(1)), []),
			m.thread(m.comment(getBeforeHours(2)), []),
			m.thread(m.comment(getBeforeHours(3)), [])
		])
		.response([
			m.thread(m.comment(getBeforeHours(3)), []),
			m.thread(m.comment(getBeforeHours(4)), []),
		])
		.finish()
	const hours = 4
	const expected = m.getDates(hours)
	expect(expected).toEqual([0, 1, 1, 2])
	const m0 = new MockResponser(rp)
	m0.fakeMock()
	const got = await i.getCommentsStats(mockVideoId, hours)
	expect(got).toEqual(expected)

	await verifyWithHttp(m0, rp, got, hours)
})

test('fast break', async () => {
	const m = new ThreadMaker()
	const rp = m
		.builder([
			m.thread(m.comment(getBeforeHours(1)), []),
			m.thread(m.comment(getBeforeHours(8)), []),
			m.thread(m.comment(getBeforeHours(1)), []) // irregular data here and below
		])
		.response([
			m.thread(m.comment(getBeforeHours(1)), []),
			m.thread(m.comment(getBeforeHours(2)), []),
		])
		.finish()

	const hours = 4
	const responser = new MockResponser(rp)
	responser.fakeMock()
	let got = await i.getCommentsStats(mockVideoId, hours)
	expect(responser.getCounts).toEqual(1)
	expect(got).toEqual([0, 1, 0, 0])
})

test('bad next page token1', async () => {
	const m = new ThreadMaker()
	const rp = m
		.builder([
			m.thread(m.comment(getBeforeHours(1)), []),
			m.thread(m.comment(getBeforeHours(2)), []),
			m.thread(m.comment(getBeforeHours(3)), []) // irregular data here and below
		])
		.response([
			m.thread(m.comment(getBeforeHours(1)), []),
			m.thread(m.comment(getBeforeHours(2)), []),
		])
		.finish()

	const corruptNext = rp.get(null)
	expect(corruptNext).toBeDefined()
	corruptNext!.nextPageToken = "--wrong"

	const hours = 4
	const responser = new MockResponser(rp)
	responser.fakeMock()
	let got = await i.getCommentsStats(mockVideoId, hours)
	expect(responser.getCounts).toEqual(2)
	expect(got).toEqual({kind: "bad", statusCode: 400})
})
