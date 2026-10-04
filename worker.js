const enc = new TextEncoder();

function toHex(buf) {
  return [...new Uint8Array(buf)].map(b => b.toString(16).padStart(2, "0")).join("");
}

async function pbkdf2(password, saltHex, iters) {
  const salt = new Uint8Array(saltHex.match(/.{2}/g).map(h => parseInt(h, 16)));
  const key = await crypto.subtle.importKey("raw", enc.encode(password), "PBKDF2", false, ["deriveBits"]);
  const bits = await crypto.subtle.deriveBits(
    { name: "PBKDF2", salt, iterations: iters, hash: "SHA-256" },
    key, 256
  );
  return toHex(bits);
}

function randomHex(n) {
  const b = new Uint8Array(n);
  crypto.getRandomValues(b);
  return [...b].map(x => x.toString(16).padStart(2, "0")).join("");
}

function json(data, status = 200) {
  return new Response(JSON.stringify(data), {
    status,
    headers: {
      "Content-Type": "application/json",
      "Access-Control-Allow-Origin": "*",
      "Access-Control-Allow-Methods": "POST, OPTIONS",
      "Access-Control-Allow-Headers": "Content-Type"
    }
  });
}

async function handleRegister(request, env) {
  const body = await request.json().catch(() => null);
  if (!body) return json({ ok: false, error: "Bad request" }, 400);
  const nickname = String(body.nickname || "").trim();
  const password = String(body.password || "");
  if (nickname.length < 3 || nickname.length > 24) return json({ ok: false, error: "Invalid nickname" }, 400);
  if (!/^[A-Za-z0-9_\-]+$/.test(nickname)) return json({ ok: false, error: "Invalid nickname" }, 400);
  if (password.length < 6 || password.length > 64) return json({ ok: false, error: "Invalid password" }, 400);

  const existing = await env.DB.prepare("SELECT id FROM users WHERE nickname = ?").bind(nickname).first();
  if (existing) return json({ ok: false, error: "Nickname taken" }, 409);

  const salt = randomHex(16);
  const passHash = await pbkdf2(password, salt, 100000);
  const now = Math.floor(Date.now() / 1000);
  const ins = await env.DB.prepare(
    "INSERT INTO users (nickname, pass_hash, salt, created_at) VALUES (?, ?, ?, ?)"
  ).bind(nickname, passHash, salt, now).run();
  const userId = ins.meta.last_row_id;

  const token = randomHex(32);
  const expires = now + 60 * 60 * 24 * 30;
  await env.DB.prepare(
    "INSERT INTO sessions (token, user_id, nickname, created_at, expires_at) VALUES (?, ?, ?, ?, ?)"
  ).bind(token, userId, nickname, now, expires).run();
  return json({ ok: true, token, nickname });
}

async function handleLogin(request, env) {
  const body = await request.json().catch(() => null);
  if (!body) return json({ ok: false, error: "Bad request" }, 400);
  const nickname = String(body.nickname || "").trim();
  const password = String(body.password || "");
  const row = await env.DB.prepare(
    "SELECT id, pass_hash, salt FROM users WHERE nickname = ?"
  ).bind(nickname).first();
  if (!row) return json({ ok: false, error: "Invalid credentials" }, 401);
  const passHash = await pbkdf2(password, row.salt, 100000);
  if (passHash !== row.pass_hash) return json({ ok: false, error: "Invalid credentials" }, 401);
  const now = Math.floor(Date.now() / 1000);
  const token = randomHex(32);
  const expires = now + 60 * 60 * 24 * 30;
  await env.DB.prepare(
    "INSERT INTO sessions (token, user_id, nickname, created_at, expires_at) VALUES (?, ?, ?, ?, ?)"
  ).bind(token, row.id, nickname, now, expires).run();
  return json({ ok: true, token, nickname });
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    if (request.method === "OPTIONS") return json({ ok: true });
    if (request.method !== "POST") return json({ ok: false, error: "Method not allowed" }, 405);
    if (url.pathname === "/register") return handleRegister(request, env);
    if (url.pathname === "/login") return handleLogin(request, env);
    return json({ ok: false, error: "Not found" }, 404);
  }
};
