import * as i from './lib';
import * as util from 'util';

import * as readline from 'node:readline';

import { stdin as input, stdout as output } from 'node:process';
import { resolve } from 'node:path';

async function repl() {
	const session = new i.Session()
	const rl = readline.createInterface({ input, output });
	//rl.question
	const q = util.promisify(rl.question).bind(rl) as any as (arg1: string) => Promise<string>
	const help = () => {
		console.log(`help:
available modes: manager|stat|pass

manager new <id>
manager stat <id>
manager extend <id> <date>

pass tryenter <id>
pass exit <id>

stats
`)
	};

	let statsUsers: Array<i.StoredUser>|undefined = undefined

	while (true) {
		const ans = await q('> ')
		const words = ans.split(/\s+/)
		if (words.length == 0) {
			continue
		}
		switch (words[0]) {
		case "manager":
			//console.log("I am a web server for sure")
			if (words.length < 2) {
				help();
				break;
			}
			switch (words[1]) {
			case "new":
				if (words.length != 3) {
					help();
					break;
				}
				try {
					session.createUser(Number.parseInt(words[2]))
				} catch (e) {
					console.log(e)
				}
				break;
			case "extend":
				if (words.length != 4) {
					help();
					break;
				}
				try {
					session.extendUserPass(Number.parseInt(words[2]), new Date(words[3]))
				} catch (e) {
					console.log(e)
				}
				break;
			case "stat":
				if (words.length != 3) {
					help();
					break;
				}
				try {
					console.log(session.userStat(Number.parseInt(words[2])))
				} catch (e) {
					console.log(e)
				}
				break;
			default:
				help();
				break;
			}
			break;
		case "pass":
			if (words.length != 3) {
				help();
				break;
			}
			switch (words[1]) {
			case "tryenter":
				try {
					console.log(session.userTryEnter(Number.parseInt(words[2])))
				} catch (e) {
					console.log(e)
				}
				break;
			case "exit":
				try {
					session.userLeave(Number.parseInt(words[2]))
				} catch (e) {
					console.log(e)
				}
				break;
			default:
				help();
				break;
			}
			break;
		case "stats":
			if (words.length != 1) {
				help();
				break;
			}
			if (statsUsers === undefined) {
				const newVals = new Array<i.StoredUser>()
				statsUsers = newVals
				session.getUsersIdsAndSubscribe((user_id, id) => {
					newVals.push(i.emptyUser(user_id, id))
				});
			}
			for (const u of statsUsers) {
				const events = session.updateUser(u)
				console.log(`${JSON.stringify(u)} // applied #${events} events`)
			}
			break;
		case "exit":
			console.log("Quit.")
			return;
		case "help":
			help()
			break
		default:
			console.log(`unknown command ${ans}`)
			break
		}
	}
}


repl()
