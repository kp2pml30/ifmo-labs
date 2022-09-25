import * as fs from 'fs';
import * as fetch from 'node-fetch';

import { strict as assert } from 'node:assert';

const apikey = fs.readFileSync('api.key','utf8').trim()

export interface BadResult {
	kind: "bad"
	statusCode: number
}

export interface OkResult {
	kind: "ok"
	json: any
}

export interface Responser {
	get(url: URL): Promise<BadResult | OkResult>
}

class DefaultResponser {
	async get(url: URL): Promise<BadResult | OkResult> {
		const response = await fetch.default(url.toString(), { method: 'GET' })
		if (!response.ok) {
			return {kind: "bad", statusCode: response.status}
		}
		return {kind: "ok", json: await response.json()}
	}
}

export function defaultSock(): Responser {
	return new DefaultResponser()
}

export interface CommentResource {
	kind: "youtube#comment",
	id: string,
	snippet: {
		authorDisplayName: string,
		authorProfileImageUrl: string,
		authorChannelUrl: string,
		authorChannelId: {
			value: string
		},
		channelId: string,
		videoId: string,
		textDisplay: string,
		textOriginal: string,
		parentId: string,
		canRate: boolean,
		viewerRating: string,
		moderationStatus: string,
		likeCount: number,
		publishedAt: string, // ISO 8601
		updatedAt: string // ISO 8601
	}
}

export interface CommentThreadResource {
	kind: "youtube#commentThread",
	id: string,
	snippet: {
		channelId: string,
		videoId: string,
		topLevelComment: CommentResource,
		canReply: boolean,
		totalReplyCount: number,
		isPublic: boolean
	},
	replies: {
		comments: CommentResource[]
	}
}

export interface ThreadListResponse {
	kind: "youtube#commentThreadListResponse",
	nextPageToken: string | null,
	pageInfo: {
		"totalResults": number,
		"resultsPerPage": number
	},
	items: CommentThreadResource[]
}

function getDatesDiffHours(a: Date, b: Date) {
	// is there a better way?
	return (a.getTime() - b.getTime()) / 36e5
}

// how to do a dependent type Array<number, hours>?
export async function getCommentsStats(sock: Responser, videoId: string, maxHours: number): Promise<BadResult | Array<number>> {
	const commentsByHour = Array<number>(maxHours).fill(0)
	const now = new Date()

	var nextPage: undefined | string

	const url = new URL("https://www.googleapis.com/youtube/v3/commentThreads");
	const params: Array<[string, string]> = [
		["key", apikey],
		["maxResults", "100"],
		["part", "snippet"],
		["order", "time"],
		["videoId", videoId]
	]
	params.forEach(element => {
		url.searchParams.append(...element)
	})

loop:
	while (true) {
		if (nextPage !== undefined) {
			url.searchParams.set("pageToken", nextPage)
		}

		const res = await sock.get(url)
		switch (res.kind) {
		case "bad":
			return res
		case "ok":
			const r = res.json as ThreadListResponse

			for (const c of r.items) {
				const date = new Date(c.snippet.topLevelComment.snippet.publishedAt)
				const hours = getDatesDiffHours(now, date)
				assert.equal(hours >= 0, true)
				if (hours >= maxHours) {
					return commentsByHour
				} else {
					commentsByHour[Math.floor(hours)]++
				}
			}

			if (typeof r.nextPageToken === "string" && r.nextPageToken !== "") {
				nextPage = r.nextPageToken
			} else {
				break loop
			}
		}
	}

	return commentsByHour
}
