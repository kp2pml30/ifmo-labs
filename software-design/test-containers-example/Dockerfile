FROM node:16

WORKDIR /usr/src/app

COPY package*.json ./
RUN npm install
RUN npm install -D ts-node


COPY tsconfig.json ./
COPY jest.config.js ./
COPY src ./src

RUN npm run build

EXPOSE 8080
CMD [ "npx", "ts-node", "-C", "ttypescript", "src/index.ts", "8080"]
