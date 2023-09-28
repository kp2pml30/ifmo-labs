"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
Object.defineProperty(exports, "__esModule", { value: true });
const i = __importStar(require("./lib"));
const util = __importStar(require("util"));
const readline = __importStar(require("node:readline"));
const node_process_1 = require("node:process");
function repl() {
    return __awaiter(this, void 0, void 0, function* () {
        const session = new i.Session();
        const rl = readline.createInterface({ input: node_process_1.stdin, output: node_process_1.stdout });
        //rl.question
        const q = util.promisify(rl.question).bind(rl);
        const help = () => {
            console.log(`help:
available modes: manager|stat|pass

manager new <id>
manager stat <id>
manager extend <id> <date>

pass tryenter <id>
pass exit <id>

stat
`);
        };
        let statsUsers = undefined;
        while (true) {
            const ans = yield q('> ');
            const words = ans.split(/\s+/);
            if (words.length == 0) {
                continue;
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
                                session.createUser(Number.parseInt(words[2]));
                            }
                            catch (e) {
                                console.log(e);
                            }
                            break;
                        case "extend":
                            if (words.length != 4) {
                                help();
                                break;
                            }
                            try {
                                session.extendUserPass(Number.parseInt(words[2]), new Date(words[3]));
                            }
                            catch (e) {
                                console.log(e);
                            }
                            break;
                        case "stat":
                            if (words.length != 3) {
                                help();
                                break;
                            }
                            try {
                                console.log(session.userStat(Number.parseInt(words[2])));
                            }
                            catch (e) {
                                console.log(e);
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
                                console.log(session.userTryEnter(Number.parseInt(words[2])));
                            }
                            catch (e) {
                                console.log(e);
                            }
                            break;
                        case "exit":
                            try {
                                session.userLeave(Number.parseInt(words[2]));
                            }
                            catch (e) {
                                console.log(e);
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
                        const newVals = new Array();
                        statsUsers = newVals;
                        session.getUsersIdsAndSubscribe((user_id, id) => {
                            newVals.push(i.emptyUser(user_id, id));
                        });
                    }
                    for (const u of statsUsers) {
                        const events = session.updateUser(u);
                        console.log(`${JSON.stringify(u)} // applied #${events} events`);
                    }
                    break;
                case "exit":
                    console.log("Quit.");
                    return;
                case "help":
                    help();
                    break;
                default:
                    console.log(`unknown command ${ans}`);
                    break;
            }
        }
    });
}
repl();
