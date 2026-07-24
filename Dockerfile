# WhatsApp bot (Baileys v7) — Render docker build.
# Pins Node 20 so Baileys' engine check passes (the bare 'node' runtime
# on Render defaults lower and the build dies in 'npm install').
FROM node:20-bookworm

WORKDIR /opt/render/project/src

# Install deps first (cache-friendly layer). package-lock.json present -> reproducible.
COPY package.json package-lock.json ./
RUN npm ci --omit=dev || npm install --omit=dev

# App source.
COPY . .

# Render injects PORT; the bot reads process.env.PORT.
EXPOSE 3001

# Tunnel disabled on Render; session/cache default to ./session ./cache (writable).
ENV DISABLE_TUNNEL=1

CMD ["node", "whats.js"]
