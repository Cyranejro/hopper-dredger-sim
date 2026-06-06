// --- ZMIENNE MASKI LĄDU ---
// Bank Cushion Effect
// sloping bank effect
// Stern Suction
// bank effect
// shallow water effect
let tileManager;
// Globalne zmienne
let depthMap = null;
let isMaskReady = false; // Kluczowa flaga blokująca fizykę

let landMask;
let isGameOver = false;
let debugMode = true;
let debugMaskMode = false;

// --- SYSTEM KAFELKÓW (TILE ENGINE) ---
const TILE_SIZE = 1024;
const MASK_WIDTH = 9168; 
const MASK_HEIGHT = 16116;
const MAP_PIXEL_WIDTH = 9168; 
const MAP_PIXEL_HEIGHT = 16116;

function preload() {
  loadGzipMask('maska.bin.gz');
}

let shipPixL, shipPixB, shipPixS;
let bKnots = 0, sKnots = 0;
let alphaL = 0, alphaR = 0;
let lastTrailTime = 0, lastBowSternTime = 0, lastUIUpdateTime = 0;

let isMobile = false;
let simulationStartTime = 0; 
let simulatedTimeDuration = 0; 

function checkDevice() {
  isMobile = "ontouchstart" in window || navigator.maxTouchPoints > 0;
}

let zoomSpeed = 0; 
let COG = 110;
let u = 3 * 0.5144;
let hdg = 2 * Math.PI * (COG / 360) - 0.5 * Math.PI;
let v = 0, r = 0;

let timeStepIdx = 0;
let currentBowThruster = 0; 

const LBP = 76.51;
const LOA = 79.6;
const B = 9.1;
const rho = 1025;
let pivotPointX = 0;

const showHeadingLine = true; 
const headingLineLength = 150; 

const MMG = {
  w: 0.3, t: 0.2, k: 0.9, AR: 4.0,
  xR: -0.45 * LBP,
  KT0: 0.39, KT1: -0.55, KT2: -0.32
};
const PROP = { gear: 4.5, propD: 1.405, shaftDist: 3.0 };

let RUDDER_FACTOR = 1.0;
let DAMPING_FACTOR = 1.0;
let currRudAngleDeg = 0;
let bowThrusterCmd = 0;
let sternThrusterCmd = 0;

let R_LEFT = { angle: 0 }, R_RIGHT = { angle: 0 };
let RUDDER_SPEED = 5.0;

let posX = 0, posY = 0;
let nL = 0, nR = 0;
let targetNL = 0, targetNR = 0, targetRud = 0;
let m, m11, m22, Jz, m66;

const BOW_THRUSTER = { power: 294000, x: 0.5 * LBP - 10, maxForce: 40000 };
const STERN_THRUSTER = { power: 294000, x: -0.5 * LBP + 10, maxForce: 40000 };

let zoom = 1.0;
let trail = [], ghostShips = [], bowTrail = [], sternTrail = [];
let trailHead = 0, bowSternHead = 0, ghostHead = 0, timerGhost = 0;
const timeSteps = [1, 2, 5, 10, 25, 50, 100];

const hopperConditions = [
  { desc: "Pusty", mass: 869400, draft: 1.59, cb: 0.8 },
  { desc: "63% Woda", mass: 1526700, draft: 2.55, cb: 0.84 },
  { desc: "100% Woda", mass: 1917000, draft: 3.12, cb: 0.88 },
  { desc: "75%W / 25%P", mass: 2110000, draft: 3.4, cb: 0.91 },
  { desc: "50%W / 50%P", mass: 2305000, draft: 3.68, cb: 0.92 },
  { desc: "25%W / 75%P", mass: 2490000, draft: 3.92, cb: 0.93 },
  { desc: "100% Piasek", mass: 2690000, draft: 4.2, cb: 0.94 }
];
let currentCond = 3;
let s = 1;

function propThrust(n, u) {
  let n_rounds = n / (60 * PROP.gear);
  if (Math.abs(n_rounds) < 0.01) return 0;
  let J = constrain((u * (1 - MMG.w)) / (n_rounds * PROP.propD + 0.001), -1.5, 1.5);
  let KT = MMG.KT0 + MMG.KT1 * J + MMG.KT2 * J * J;
  let T = rho * n_rounds * Math.abs(n_rounds) * Math.pow(PROP.propD, 4) * KT; 
  if (n < 0) T *= 0.45; 
  return (1 - MMG.t) * T;
}

function rudder(delta, u, v, r, T) {
  let slipstream = constrain(MMG.k * Math.sqrt(Math.abs(T) / (rho * PROP.propD * PROP.propD + 0.001)), 0, 3);
  let uR = Math.max(0.0, u * (1 - MMG.w) + slipstream);
  let vR = v + MMG.xR * r;
  let UR = Math.sqrt(uR * uR + vR * vR);
  let alpha = constrain(delta - Math.atan2(vR, uR), radians(-35), radians(-35) * -1);
  let CL = constrain((6.13 * alpha) / (1 + 2.25 * Math.abs(alpha)), -1.8, 1.8);

  let FN = (0.5 * rho * MMG.AR * UR * UR * CL) / Math.sqrt(hopperConditions[currentCond].draft / 1.59);
  return {
    X: -FN * Math.sin(delta) * RUDDER_FACTOR,
    Y: FN * Math.cos(delta) * RUDDER_FACTOR,
    N: FN * Math.cos(delta) * MMG.xR * RUDDER_FACTOR,
    alpha: degrees(alpha)
  };
}

function hull(u, v, r, s) {
  let U = Math.sqrt(u * u + v * v) + 0.001;
  let v_ = v / U, r_ = (r * LBP) / U;
  let draftFactor = s.draft / 1.59;
  let R_fric = -(0.028 * (s.cb / 0.8)) * 0.5 * rho * LBP * s.draft * u * Math.abs(u);
  let speedFactor = Math.tanh(U / 0.5);
  
  let Y = speedFactor * (0.5 * rho * LBP * s.draft * U * U * (-0.5 * v_ + 0.05 * r_ - v_ * Math.abs(v_))) + (1 - speedFactor) * (-0.2 * rho * LBP * s.draft * v);
  let N = speedFactor * (0.8 * rho * LBP * LBP * s.draft * U * U * (-0.05 * v_ - 0.02 * r_ * draftFactor - 0.06 * r_ * Math.abs(r_) * draftFactor)) + (1 - speedFactor) * (-0.1 * rho * LBP * LBP * r);
  
  return { X: R_fric, Y, N };
}

function getThrusterForce(u, v, r, cmd, xPos) {
  let speed = Math.sqrt(u * u + v * v + Math.pow(r * xPos, 2)); 
  let localVy = v + r * xPos; 
  let Y = (40000 * cmd * Math.exp(-Math.pow(speed / 0.8, 2))) + (-0.5 * rho * localVy * Math.abs(localVy) * 1.2);
  return { Y, N: Y * xPos };
}

function computePivotPoint(u, v, r) {
  // Jeśli statek się nie obraca, chronimy przed dzieleniem przez zero
  if (Math.abs(r) < 0.001) {
    let speed = Math.sqrt(u * u + v * v);
    if (speed < 0.1) return 0; // Statek stoi = PP na środku
    return 0; 
  }
  
  // Czysta kinematyka: punkt, gdzie prędkość boczna się zeruje
  let rawPP = -v / r;
  
  // Ogranicznik "na wszelki wypadek", żeby PP nie uciekł z ekranu przy anomaliach
  return constrain(rawPP, -LBP, LBP); 
}

function applyHopperPhysics() {
  let currentS = hopperConditions[currentCond];
  m = currentS.mass; 
  Jz = 0.05 * m * LBP * LBP; 
  m11 = -0.15 * m; 
  m22 = -0.9 * m; 
  m66 = -4.0 * Jz; 
  let f = m / 869400;
  MMG.w = 0.28 + 0.12 * (f - 1);
  MMG.t = 0.18 + 0.1 * (f - 1);
}

function setup() {
  createCanvas(windowWidth, windowHeight);
  checkDevice();
  applyHopperPhysics();
  setupHTMLUI();
  // Start w lewym górnym rogu mapy
  posX = 512; 
  posY = 512;
  hdg = hdg; // Zwrot w prawo lub dowolny zgodny z fizyką

  tileManager = new TileManager();
  
  shipPixL = LBP;
  shipPixB = B;
  shipPixS = PROP.shaftDist;
  simulationStartTime = millis(); 
  // landMask.loadPixels();
}

function updatePhysics(dt) {
  if (isGameOver) return;
  
  simulatedTimeDuration += dt;
  let currentS = hopperConditions[currentCond];

  // 1. ZBIERAMY DANE HYDRODYNAMICZNE
 let hydro = scanHydrodynamics(posX, posY, hdg, LBP, B, currentS.draft, u, v, r, pivotPointX);

  if (hydro.isColliding) {
    isGameOver = true;
    return; // Przerwij dalsze liczenie!
  }
  
  if (keyIsDown(65)) targetRud = Math.min(35, targetRud + 10 * dt);
  if (keyIsDown(68)) targetRud = Math.max(-35, targetRud - 10 * dt);
  
  sternThrusterCmd = keyIsDown(90) ? 1 : (keyIsDown(67) ? -1 : 0);

  let expFactor = 1 - Math.exp(-dt / 10);
  nL += (targetNL - nL) * expFactor;
  nR += (targetNR - nR) * expFactor;

  let maxMove = RUDDER_SPEED * dt;
  R_LEFT.angle += constrain(targetRud - R_LEFT.angle, -maxMove, maxMove);
  R_RIGHT.angle += constrain(targetRud - R_RIGHT.angle, -maxMove, maxMove);
  currRudAngleDeg = R_LEFT.angle;
  currentBowThruster += (bowThrusterCmd - currentBowThruster) * (dt / 0.3);

  // 2. OBLICZANIE STANDARDOWYCH SIŁ KADŁUBA I NAPĘDU
  let HP = hull(u, v, r, currentS);
  
  let TL = propThrust(nL, u), TR = propThrust(nR, u);
  let RL = rudder(radians(R_LEFT.angle), u, v, r, TL);
  let RR = rudder(radians(R_RIGHT.angle), u, v, r, TR);
  let BT = getThrusterForce(u, v, r, currentBowThruster, BOW_THRUSTER.x);
  let ST = getThrusterForce(u, v, r, sternThrusterCmd, STERN_THRUSTER.x);
  // --- POPRAWKI FIZYKI DLA STERA STRUMIENIOWEGO ---

// 1. ZABICIE FAKE'OWEGO PRZYSPIESZENIA DO PRZODU (Cross-flow drag)
// Kiedy statek ma duże 'v' i 'r', woda hamuje jego ruch do przodu.
// To skontruje człon (m * v * r) z równań Eulera.
let crossDragX = -0.50 * rho * LBP * currentS.draft * Math.abs(v * r) * 1.5; 
// Jeśli statek mimo to płynie do przodu, zwiększ mnożnik '1.5' na np. '3.0'
HP.X += crossDragX; 

// 2. ZABLOKOWANIE ŚLIZGANIA W BOK (Sway Drag)
// Wymusza na statku opieranie się wodzie przy użyciu BT
let swayDragY = -0.5 * rho * LBP * currentS.draft * 2.0 * v * Math.abs(v);
HP.Y += swayDragY;

// 3. DODATKOWE TŁUMIENIE OBROTU (Yaw Damping)
// Zapewnia, że statek nie rozkręci się do absurdalnych prędkości
let yawDragN = -0.5 * rho * Math.pow(LBP, 3) * currentS.draft * 0.2 * r * Math.abs(r);
HP.N += yawDragN;
  alphaL = RL.alpha; alphaR = RR.alpha;

// 3. WSPÓŁCZYNNIKI I APLIKACJA EFEKTÓW ŚRODOWISKOWYCH (MAGIA!)
  let squatResistanceMulti = 1.0 + (hydro.squatFactor * 2.5); 
  HP.X *= squatResistanceMulti;

  // PROBLEM 3: Velocity Saturation (Ochrona przed wybuchem V^2)
  // Przejście z czystego V^2 (niskie prędkości) do niemal liniowego V (wysokie prędkości).
  let safeU = Math.abs(u);
  let velocitySaturation = 1.0 / (1.0 + safeU * 0.25); 
  
  let bankForceFactorY = 0.2 * rho * LBP * currentS.draft * (u * safeU) * velocitySaturation; 
  let bankForceFactorN = 0.005 * rho * LBP * LBP * currentS.draft * (u * safeU) * velocitySaturation;

  let targetENV_Y = hydro.bankY * bankForceFactorY;
  let targetENV_N = hydro.bankN * bankForceFactorN;

  // PROBLEM 4: Hysteresis / Pamięć przepływu (Filtr dolnoprzepustowy)
  // Inicjalizacja zmiennych w locie, jeśli jeszcze nie istnieją
  if (typeof window.filteredEnvY === 'undefined') {
    window.filteredEnvY = 0;
    window.filteredEnvN = 0;
  }

  // filterRate = 1.5 oznacza, że siła potrzebuje ok. 0.6 sekundy na pełne "zbudowanie się" lub "odklejenie"
  let filterRate = 0.5; 
  let expFilter = 1.0 - Math.exp(-dt * filterRate);

  window.filteredEnvY += (targetENV_Y - window.filteredEnvY) * expFilter;
  window.filteredEnvN += (targetENV_N - window.filteredEnvN) * expFilter;

  let ENV_Y = window.filteredEnvY;
  let ENV_N = window.filteredEnvN;

  // Ograniczniki wciąż tu są jako absolutny "hard limit" dla glitchy, ale rzadko będą teraz uderzane
  ENV_Y = constrain(ENV_Y, -500000, 500000); 
  ENV_N = constrain(ENV_N, -8000000, 8000000);

  // ---> DODAJ TO PONIŻEJ OGRANICZEŃ CONSTRAIN <---
  // Zapisujemy parametry do globalnego obiektu do celów rysowania
  window.hydroDebug = {
    squat: squatResistanceMulti,
    forceY: ENV_Y,
    forceN: ENV_N
  };

  // 4. APLIKACJA WSZYSTKICH SIŁ NA MASY
  u += ((HP.X + TL + TR + RL.X + RR.X) + (m + m22) * v * r) / (m - m11) * dt;
  
  // Zauważ dodane ENV_Y oraz ENV_N do równań v i r!
  v += ((HP.Y + RL.Y + RR.Y + BT.Y + ST.Y + ENV_Y) - (m + m11) * u * r) / (m - m22) * dt;
  r += ((HP.N + RL.N + RR.N + BT.N + ST.N + ENV_N) + (TL - TR) * (PROP.shaftDist * 0.5) + 0.05 * (TL - TR)) / (Jz - m66) * dt;

  pivotPointX = computePivotPoint(u, v, r);
  hdg += r * dt;
  
  let cosH = Math.cos(hdg), sinH = Math.sin(hdg);
  posX += (u * cosH - v * sinH) * dt;
  posY += (u * sinH + v * cosH) * dt;
  
  if (isCollidingWithLand()) {
    isGameOver = true;
  }

  u = constrain(u, -20, 20); v = constrain(v, -10, 10); r = constrain(r, -5, 5);
  bKnots = (v + r * (LBP * 0.5)) * 1.94384;
  sKnots = (v + r * (-LBP * 0.5)) * 1.94384;
}

function updateVisualHistory() {
  if (simulatedTimeDuration - lastTrailTime >= 1.0) {
    let maxTrail = 600;
    if (trail.length < maxTrail) trail.push({ x: posX, y: posY });
    else {
      trail[trailHead] = { x: posX, y: posY };
      trailHead = (trailHead + 1) % maxTrail;
    }
    lastTrailTime = simulatedTimeDuration;
  }

  if (simulatedTimeDuration - lastBowSternTime >= 0.5) {
    let cosH = Math.cos(hdg), sinH = Math.sin(hdg);
    let bowPos = { x: (posX + (LBP * 0.5) * cosH), y: (posY + (LBP * 0.5) * sinH) };
    let sternPos = { x: (posX + (-LBP * 0.5) * cosH), y: (posY + (-LBP * 0.5) * sinH) };
    let maxElements = 60;
    
    if (bowTrail.length < maxElements) {
      bowTrail.push(bowPos);
      sternTrail.push(sternPos);
    } else {
      bowTrail[bowSternHead] = bowPos;
      sternTrail[bowSternHead] = sternPos;
      bowSternHead = (bowSternHead + 1) % maxElements;
    }
    lastBowSternTime = simulatedTimeDuration;
  }

  timerGhost += deltaTime / 1000;
  if (timerGhost >= 5) {
    let maxGhosts = 40;
    if (ghostShips.length < maxGhosts) ghostShips.push({ x: posX, y: posY, h: hdg });
    else {
      ghostShips[ghostHead] = { x: posX, y: posY, h: hdg };
      ghostHead = (ghostHead + 1) % maxGhosts;
    }
    timerGhost = 0;
  }
}

function draw() {
  // 1. EKRAN ŁADOWANIA - blokuje główną pętlę
  if (!isMaskReady) {
    background(20);
    fill(255);
    textAlign(CENTER, CENTER);
    textSize(24);
    text("Rozpakowywanie maski fizyki...", width / 2, height / 2);
    return; // Przerwanie draw() - kod poniżej się nie wykona!
  }
  // 1. OBLICZENIA FIZYKI
  let dtFrame = (1 / 60) * timeSteps[timeStepIdx];
  let steps = Math.ceil(dtFrame / 0.02);
  let dt = dtFrame / steps;

  for (let i = 0; i < steps; i++) updatePhysics(dt);
  updateVisualHistory();

  // 2. AKTUALIZACJA INTERFEJSU (UI) - co 500ms
  let currentMillis = millis();
  if (currentMillis - lastUIUpdateTime >= 500) {
    let hdgDeg = ((hdg * 180) / Math.PI + 90) % 360;
    if (hdgDeg < 0) hdgDeg += 360;
    let stwKnots = u / 0.5144;

    let formatHdg = `${hdgDeg.toFixed(1)}°`;
    let formatStw = `${stwKnots.toFixed(1)} kn`;

    document.getElementById("val-hdg").innerText = formatHdg;
    document.getElementById("val-stw").innerText = formatStw;
    document.getElementById("val-rot").innerText = `${(r * (180 / Math.PI) * 60).toFixed(1)}°/m`;
    document.getElementById("val-cog").innerText = formatHdg;
    document.getElementById("val-sog").innerText = formatStw;

    // OPTYMALIZACJA DOM: Aktualizacja rozszerzonych statystyk tylko gdy menu jest widoczne
    if (document.getElementById("stats-menu").style.display === "block") {
      let currentVel = Math.sqrt(u * u + v * v);
      let totalSeconds = Math.floor(simulatedTimeDuration);
      let timeDrift = Math.max(0, (currentMillis - simulationStartTime) / 1000 - simulatedTimeDuration / timeSteps[timeStepIdx]);
      let currentFPS = frameRate();
      let mem = window.performance?.memory;

      document.getElementById("val-bow-side").innerText = `${Math.abs(bKnots).toFixed(1)} kn ${bKnots > 0 ? "R" : "L"}`;
      document.getElementById("val-stern-side").innerText = `${Math.abs(sKnots).toFixed(1)} kn ${sKnots > 0 ? "R" : "L"}`;
      document.getElementById("val-aoa-lr").innerText = `${alphaL.toFixed(1)}° / ${alphaR.toFixed(1)}°`;
      document.getElementById("val-u-vel").innerText = `${u.toFixed(2)} m/s`;
      document.getElementById("val-v-vel").innerText = `${v.toFixed(2)} m/s`;
      document.getElementById("val-r-vel").innerText = `${r.toFixed(3)} rad/s`;

      document.getElementById("val-turn-dia").innerText = (Math.abs(r) > 0.001 && currentVel > 0.2) 
        ? `${((currentVel / Math.abs(r)) * 2).toFixed(1)} m` 
        : "N/A";

      // Formatowanie czasu symulacji
      let h = Math.floor(totalSeconds / 3600);
      let m = String(Math.floor((totalSeconds % 3600) / 60)).padStart(2, '0');
      let s = String(totalSeconds % 60).padStart(2, '0');
      document.getElementById("val-sim-time").innerText = h > 0 ? `${String(h).padStart(2, '0')}:${m}:${s}` : `${m}:${s}`;

      // Drift i kolory
      let driftEl = document.getElementById("val-drift");
      driftEl.innerText = `${timeDrift.toFixed(1)} s`;
      driftEl.style.color = timeDrift > 5.0 ? "#ff5050" : (timeDrift > 1.0 ? "#ffc800" : "#00c864");

      // Wydajność
      document.getElementById("val-fps").innerText = currentFPS.toFixed(0);
      document.getElementById("val-ram").innerText = mem ? `${(mem.usedJSHeapSize / 1048576).toFixed(1)} MB` : "N/A";

      let perfStatusEl = document.getElementById("val-perf-status");
      if (deltaTime > 50) { 
        perfStatusEl.innerText = "LAG SPIKE"; perfStatusEl.style.color = "#ff5050"; 
      } else if (currentFPS < 30) { 
        perfStatusEl.innerText = "LOW FPS"; perfStatusEl.style.color = "#ffc800"; 
      } else { 
        perfStatusEl.innerText = "SMOOTH"; perfStatusEl.style.color = "#00c864"; 
      }
    }
    
    document.getElementById("val-time-display").innerText = `${timeSteps[timeStepIdx]}x`;
    document.getElementById("val-zoom-display").innerText = `${zoom.toFixed(1)}x`;
    lastUIUpdateTime = currentMillis;
  }

  // 3. RENDEROWANIE ŚRODOWISKA I OBIEKTÓW
  background(200);

  // Aktualizacja zooma przed transformacjami
  if (zoomSpeed !== 0) zoom = constrain(zoom + zoomSpeed, 0.5, 3.0);

  push();
  translate(width * 0.5, height * 0.5);
  scale(zoom);
  translate(-posX, -posY);

  // Rysowanie mapy i śladów
  tileManager.draw(posX, posY, zoom);

  if (debugMaskMode) {
    drawMaskRadar();
  }

  drawTrail();
  drawBowSternTrails();
  drawGhosts();

  // Rysowanie statku
  push();
  translate(posX, posY);
  drawShip();
  pop();
  
  // Rysowanie sensorów i powrót do głównej macierzy
  drawSensors();
  pop();

  // 4. RENDEROWANIE NAKŁADEK UI NA WIERZCHU
  drawHeaderUI();
  drawScale();
  drawControlUI();
}

function drawShip() {
  push();
  rotate(hdg);

  fill(80); 
  stroke(0);
  strokeWeight(1.5 / zoom);
  
  beginShape();
  vertex(shipPixL * 0.45, -shipPixB * 0.45);
  bezierVertex(shipPixL * 0.55, -shipPixB * 0.5, shipPixL * 0.55, shipPixB * 0.5, shipPixL * 0.45, shipPixB * 0.45);
  vertex(-shipPixL * 0.45, shipPixB * 0.45);
  vertex(-shipPixL * 0.5, shipPixB * 0.2);
  vertex(-shipPixL * 0.5, -shipPixB * 0.2);
  vertex(-shipPixL * 0.45, -shipPixB * 0.45);
  endShape(CLOSE);

  fill(120); 
  rectMode(CENTER);
  rect(-shipPixL * 0.25, 0, shipPixL * 0.2, shipPixB * 0.8, 2);

  fill(30);
  rect(shipPixL * 0.1, 0, shipPixL * 0.4, shipPixB * 0.6, 1);

  if (showHeadingLine) {
    stroke(0, 0, 0, 180);
    strokeWeight(1.5 / zoom);
    line(shipPixL * 0.5, 0, shipPixL * 0.5 + headingLineLength, 0);
  }

  stroke(255, 0, 0);
  strokeWeight(2);
  push();
  translate(-shipPixL * 0.5, -shipPixS * 0.5);
  rotate(radians(R_LEFT.angle));
  line(0, 0, -3, 0);
  pop();
  push();
  translate(-shipPixL * 0.5, shipPixS * 0.5);
  rotate(radians(R_RIGHT.angle));
  line(0, 0, -3, 0);
  pop();

  pop();

  if (pivotPointX !== null) {
    push();
    rotate(hdg);
    translate(pivotPointX, 0);
    fill(255, 0, 0);
    textSize(10);
    text(pivotPointX.toFixed(1) + " m", 5, 4);
    ellipse(0, 0, 6, 6);
    pop();
  }
}

function drawGhosts() {
  noFill();
  stroke(180, 180, 180, 80);
  strokeWeight(0.5);
  rectMode(CENTER);
  for (let i = 0; i < ghostShips.length; i++) {
    let g = ghostShips[(ghostHead + i) % ghostShips.length];
    push();
    translate(g.x, g.y);
    rotate(g.h);
    rect(0, 0, LBP, B, 2);
    pop();
  }
}

function drawTrail() {
  noFill();
  stroke(0, 255);
  strokeWeight(1);
  beginShape();
  for (let i = 0; i < trail.length; i++) {
    let p = trail[(trailHead + i) % trail.length];
    vertex(p.x, p.y);
  }
  endShape();
}

function drawBowSternTrails() {
  noFill();
  strokeWeight(1 / zoom); 

  stroke(0, 200, 100, 150);
  beginShape();
  for (let i = 0; i < bowTrail.length; i++) {
    let p = bowTrail[(bowSternHead + i) % bowTrail.length];
    vertex(p.x, p.y);
  }
  endShape(); 

  stroke(220, 50, 50, 150);
  beginShape();
  for (let i = 0; i < sternTrail.length; i++) {
    let p = sternTrail[(bowSternHead + i) % sternTrail.length];
    vertex(p.x, p.y);
  }
  endShape();
}

function drawHeaderUI() {
  fill(20, 25, 35, 230);
  noStroke();
  rect(0, 0, 160, 40, 0, 0, 10, 0);
  fill(255);
  textStyle(BOLD);
  textSize(14);
  text(`COND: ${hopperConditions[currentCond].desc} + T: ${hopperConditions[currentCond].draft}`, 20, 25);
  textStyle(NORMAL);
}

function drawScale() {
  push();
  let scaleLengthMeters = zoom < 0.5 ? 200 : (zoom > 2 ? 10 : 50);
  let pixelWidth = scaleLengthMeters * zoom;
  let x = width - 700, y = height - 50;
  stroke(0); strokeWeight(2);
  line(x, y, x + pixelWidth, y);
  line(x, y - 5, x, y + 5);
  line(x + pixelWidth, y - 5, x + pixelWidth, y + 5);
  noStroke(); fill(0); textStyle(BOLD); textAlign(CENTER);
  text(scaleLengthMeters + " m", x + pixelWidth * 0.5, y - 10);
  pop();
}

function keyPressed() {
  const RPM_STEP = 50;
  if (key === "w" || key === "W") {
    if (targetNL < 0) { targetNL += RPM_STEP; if (targetNL > -600) targetNL = 0; }
    else if (targetNL === 0) targetNL = 600;
    else targetNL = Math.min(1800, targetNL + RPM_STEP);
  }
  if (key === "s" || key === "S") {
    if (targetNL > 0) { targetNL -= RPM_STEP; if (targetNL < 600) targetNL = 0; }
    else if (targetNL === 0) targetNL = -600;
    else targetNL = Math.max(-1800, targetNL - RPM_STEP);
  }
  if (key === "i" || key === "I") {
    if (targetNR < 0) { targetNR += RPM_STEP; if (targetNR > -600) targetNR = 0; }
    else if (targetNR === 0) targetNR = 600;
    else targetNR = Math.min(1800, targetNR + RPM_STEP);
  }
  if (key === "k" || key === "K") {
    if (targetNR > 0) { targetNR -= RPM_STEP; if (targetNR < 600) targetNR = 0; }
    else if (targetNR === 0) targetNR = -600;
    else targetNR = Math.max(-1800, targetNR - RPM_STEP);
  }
  if (key === "=" || key === "+") timeStepIdx = Math.min(timeSteps.length - 1, timeStepIdx + 1);
  if (key === "-" || key === "_") timeStepIdx = Math.max(0, timeStepIdx - 1);
  if (key === "0") {
    u = v = r = posX = posY = nL = nR = targetNL = targetNR = targetRud = 0;
    hdg = -Math.PI * 0.5;
    trail = []; ghostShips = [];
  }
  if (key >= "1" && key <= "7") {
    currentCond = int(key) - 1;
    applyHopperPhysics();
  }
  if (key === " ") targetRud = 0;
  if (key === "r" || key === "R") { targetNL = 600; targetNR = 600; }
  if (key === "t" || key === "T") { targetNL = 1500; targetNR = 1500; }
  if (key === "[") RUDDER_FACTOR = Math.max(0, RUDDER_FACTOR - 0.05);
  if (key === "]") RUDDER_FACTOR += 0.05;
  if (key === ";") DAMPING_FACTOR = Math.max(0, DAMPING_FACTOR - 0.1);
  if (key === "'") DAMPING_FACTOR += 0.1;
  if (key === "e" || key === "E") bowThrusterCmd = Math.min(1.0, bowThrusterCmd + 0.1);
  if (key === "q" || key === "Q") bowThrusterCmd = Math.max(-1.0, bowThrusterCmd - 0.1);
}

function mouseWheel(event) {
  zoom = constrain(zoom - event.delta * 0.001, 0.5, 3);
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  checkDevice();
}

function drawControlUI() {
  push();
  rectMode(CORNER); textAlign(CENTER, CENTER); textStyle(BOLD);

  let inputs = [];
  if (touches.length > 0) {
    for (let t of touches) inputs.push({ x: t.x, y: t.y });
  } else if (mouseIsPressed) {
    inputs.push({ x: mouseX, y: mouseY });
  }

  let isLandscape = width > height;
  let engW, engH, engY, lEngX, rEngX, btW, btH, btY, btX, rudW, rudH, rudY, rudX;

  if (isLandscape) {
    engW = width * 0.08; engH = height * 0.35; lEngX = width * 0.025; rEngX = lEngX + engW * 1.5; engY = height - engH - 30;
    btW = engW * 2.5; btH = engW * 0.5; btX = width * 0.025; btY = engY - btH - engW * 1.5;
    rudW = btW * 2; rudH = btH; rudX = width - rudW - 30; rudY = height - rudH - 30;
  } else {
    engW = width * 0.16; engH = height * 0.35; lEngX = width * 0.04; rEngX = lEngX + engW * 1.5; engY = height - engH - 30;
    btW = width * 0.45; btH = 60; btX = width * 0.04; btY = engY - btH - engW - 20;
    rudW = width * 0.45; rudH = 70; rudX = width * 0.51; rudY = height - rudH - 30;
  }

  for (let t of inputs) {
    let margin = engW * 0.5;
    if (t.x > lEngX - margin && t.x < lEngX + engW + margin && t.y > engY - margin && t.y < engY + engH + margin) {
      let raw = map(t.y, engY + engH - 3, engY + 3, -1800, 1800);
      targetNL = Math.abs(raw) < 250 ? 0 : (raw > 0 && raw < 600 ? 600 : (raw < 0 && raw > -600 ? -600 : constrain(raw, -1800, 1800)));
    }
    if (t.x > rEngX - margin && t.x < rEngX + engW + margin && t.y > engY - margin && t.y < engY + engH + margin) {
      let raw = map(t.y, engY + engH - 3, engY + 3, -1800, 1800);
      targetNR = Math.abs(raw) < 250 ? 0 : (raw > 0 && raw < 600 ? 600 : (raw < 0 && raw > -600 ? -600 : constrain(raw, -1800, 1800)));
    }
    if (t.x > btX - margin && t.x < t.x + btW + margin && t.y > btY - margin && t.y < btY + btH + margin) {
      let raw = map(t.x, btX + 3, btX + btW - 3, -1, 1);
      bowThrusterCmd = Math.abs(raw) < 0.15 ? 0 : constrain(raw, -1, 1);
    }
    if (t.x > rudX - margin && t.x < rudX + rudW + margin && t.y > rudY - margin && t.y < rudY + rudH + margin) {
      let raw = map(t.x, rudX + 3, rudX + rudW - 3, 35, -35);
      targetRud = Math.abs(raw) < 4 ? 0 : constrain(raw, -35, 35);
    }
  }

  fill(20, 25, 35, 180); stroke(100, 200, 255, 100); strokeWeight(2);
  rect(lEngX, engY, engW, engH, 10); rect(rEngX, engY, engW, engH, 10);
  rect(btX, btY, btW, btH, 10); rect(rudX, rudY, rudW, rudH, 10);

  noStroke(); rectMode(CORNERS);
  fill(0, 255, 100, 60);
  rect(lEngX + 2, engY + engH * 0.5, lEngX + engW - 2, map(nL, -1800, 1800, engY + engH - 3, engY + 3), 8);
  rect(rEngX + 2, engY + engH * 0.5, rEngX + engW - 2, map(nR, -1800, 1800, engY + engH - 3, engY + 3), 8);
  fill(0, 180, 255, 60);
  rect(btX + btW * 0.5, btY + 2, map(currentBowThruster, -1, 1, btX + 3, btX + btW - 3), btY + btH - 2, 8);
  fill(255, 200, 0, 60);
  rect(rudX + rudW * 0.5, rudY + 2, map(currRudAngleDeg, 35, -35, rudX + 3, rudX + rudW - 3), rudY + rudH - 2, 8);

  rectMode(CORNER); stroke(255, 100);
  line(lEngX, engY + engH * 0.5, lEngX + engW, engY + engH * 0.5);
  line(rEngX, engY + engH * 0.5, rEngX + engW, engY + engH * 0.5);
  line(btX + btW * 0.5, btY, btX + btW * 0.5, btY + btH);
  line(rudX + rudW * 0.5, rudY, rudX + rudW * 0.5, rudY + rudH);

  noStroke(); rectMode(CENTER);
  fill(targetNL === 0 ? color(255, 80, 80) : color(0, 255, 100));
  rect(lEngX + engW * 0.5, map(targetNL, -1800, 1800, engY + engH - 3, engY + 3), engW + 16, 6, 6);
  fill(targetNR === 0 ? color(255, 80, 80) : color(0, 255, 100));
  rect(rEngX + engW * 0.5, map(targetNR, -1800, 1800, engY + engH - 3, engY + 3), engW + 16, 6, 6);
  fill(0, 180, 255);
  rect(map(bowThrusterCmd, -1, 1, btX + 3, btX + btW - 3), btY + btH * 0.5, 6, btH + 16, 6);
  fill(255, 200, 0);
  rect(map(targetRud, 35, -35, rudX + 3, rudX + rudW - 3), rudY + rudH * 0.5, 6, rudH + 16, 6);

  let txtL = "PS-RPM: " + Math.round(nL), txtR = "SB-RPM: " + Math.round(nR);
  let txtBT = "BOW THRUST: " + Math.round(currentBowThruster * 100) + "%", txtRud = "RUDDER: " + currRudAngleDeg.toFixed(1) + "°";

  textSize(11); fill(0, 180);
  rect(lEngX + engW * 0.5, engY - 15, textWidth(txtL) + 12, 20, 4);
  rect(rEngX + engW * 0.5, engY - 15, textWidth(txtR) + 12, 20, 4);
  rect(btX + btW * 0.5, btY - 15, textWidth(txtBT) + 12, 20, 4);
  rect(rudX + rudW * 0.5, rudY - 15, textWidth(txtRud) + 12, 20, 4);

  fill(255);
  text(txtL, lEngX + engW * 0.5, engY - 15); text(txtR, rEngX + engW * 0.5, engY - 15);
  text(txtBT, btX + btW * 0.5, btY - 15); text(txtRud, rudX + rudW * 0.5, rudY - 15);
  pop();
}

function setupHTMLUI() {
  document.getElementById("btn-stats").onclick = () => {
    let statsMenu = document.getElementById("stats-menu");
    let settingsMenu = document.getElementById("settings-menu");
    if (settingsMenu) settingsMenu.style.display = "none";
    statsMenu.style.display = statsMenu.style.display === "block" ? "none" : "block";
  };
  
  document.getElementById("btn-gear").onclick = () => {
    let menu = document.getElementById("settings-menu");
    menu.style.display = menu.style.display === "block" ? "none" : "block";
  };

  document.getElementById("btn-fullscreen").onclick = () => { fullscreen(!fullscreen()); };

  document.addEventListener("fullscreenchange", () => {
    document.getElementById("btn-fullscreen").innerText = (document.fullscreenElement !== null) ? "Zamknij Ekran ✖" : "Pełny Ekran 📱";
  });

  document.getElementById("btn-time-minus").onclick = () => (timeStepIdx = Math.max(0, timeStepIdx - 1));
  document.getElementById("btn-time-plus").onclick = () => (timeStepIdx = Math.min(timeSteps.length - 1, timeStepIdx + 1));
  document.getElementById("btn-zoom-minus").onclick = () => { zoom = constrain(zoom - 0.2, 0.5, 3.0); };
  document.getElementById("btn-zoom-plus").onclick = () => { zoom = constrain(zoom + 0.2, 0.5, 3.0); };

  setCondition(currentCond !== undefined ? currentCond : 0);
  
  let restartBtn = document.getElementById('btn-restart');
  if (restartBtn) restartBtn.addEventListener('click', restartSimulation);
}

function setCondition(idx) {
  currentCond = idx;
  applyHopperPhysics();
  let btns = document.getElementsByClassName("btn-cond");
  for (let i = 0; i < btns.length; i++) {
    if (i === idx) btns[i].classList.add("active");
    else btns[i].classList.remove("active");
  }
}

function startZoom(speed) { zoomSpeed = speed; }
function stopZoom() { zoomSpeed = 0; }

function restartSimulation() {
  isGameOver = false;
  posX = 1200;
  posY = 700;
  hdg = radians(30);
  bKnots = sKnots = u = v = r = alphaL = alphaR = nL = nR = targetNL = targetNR = targetRud = simulatedTimeDuration = 0;
  simulationStartTime = millis();
  console.log("Symulacja zrestartowana.");
}
function getMaskValueAt(worldX, worldY) {
  if (!depthMap) return 0; 

  // --- 1. SKALOWANIE (METRY NA PIKSELE) ---
  // Rozmiar obrazka statku (225px) / Długość rzeczywista (76.51m)
  const METERS_TO_PIXELS = 225 / 76.51; 

  // --- 2. KOREKTA PRZESUNIĘCIA (OFFSET) ---
  // Zmieniaj te wartości (np. 100, -50), jeśli radar nie pokrywa się z mapą
  const OFFSET_X = 0; 
  const OFFSET_Y = 0;

  // Przeliczenie pozycji ze świata gry (metry) na pozycję w tablicy (piksele)
  let px = Math.floor(worldX * METERS_TO_PIXELS) + OFFSET_X;
  let py = Math.floor(worldY * METERS_TO_PIXELS) + OFFSET_Y;
  
  if (px >= 0 && px < MASK_WIDTH && py >= 0 && py < MASK_HEIGHT) {
    return depthMap[py * MASK_WIDTH + px];
  }
  
  return 0; // Woda poza mapą
}
class TileManager {
  constructor() {
    this.nativeTileSize = 1024; // Prawdziwy rozmiar pliku w pikselach
    
    // --- SKALOWANIE DO METRÓW ---
    // Statek ma LBP = 76.51m i na mapie zajmuje 225px.
    // Przeliczamy 1024px kafelka na rzeczywiste metry w świecie gry.
    this.meterTileSize = (76.51 / 225) * this.nativeTileSize; // Wynik: ~348.16 m
    
    this.cols = 9; // 0 do 8
    this.rows = 16; // 0 do 15
    
    this.tileCache = new Map(); // Pamięć podręczna na wczytane kafelki
    this.loadingTiles = new Set(); // Zapobiega wielokrotnemu wczytywaniu tego samego kafelka
    
    // Ścieżka do kafelków: gdansk/TILES/tile_col_row.jpg
    this.basePath = 'gdansk/tiles/tile_'; 
  }

  // Funkcja generująca klucz dla kafelka
  getTileKey(col, row) {
    return `${col}_${row}`;
  }

  // Asynchroniczne ładowanie kafelka (no-blocking UI)
  asyncRequestTile(col, row) {
    const key = this.getTileKey(col, row);
    if (this.tileCache.has(key) || this.loadingTiles.has(key)) return;

    this.loadingTiles.add(key);
    
    // Wczytywanie pliku .jpg
    const path = `${this.basePath}${col}_${row}.webp`; // Używamy .webp dla lepszej kompresji, ale można zmienić na .jpg jeśli nie jest obsługiwany
    
    loadImage(path, 
      (img) => {
        this.tileCache.set(key, img);
        this.loadingTiles.delete(key);
      },
      () => {
        // W razie braku kafelka (błąd ładowania 404) odblokowujemy kolejkę
        this.loadingTiles.delete(key);
      }
    );
  }

  // Główna funkcja renderująca (Culling System)
  draw(camX, camY, zoom) {
    // 1. Obliczamy granice ekranu w METRACH świata gry (z uwzględnieniem przybliżenia)
    const halfW = (width / 2) / zoom;
    const halfH = (height / 2) / zoom;
    
    const screenLeft = camX - halfW;
    const screenRight = camX + halfW;
    const screenTop = camY - halfH;
    const screenBottom = camY + halfH;

    // 2. Obliczamy indeksy kafelków bazując na rozmiarze w metrach (meterTileSize)
    const startCol = Math.max(0, Math.floor(screenLeft / this.meterTileSize));
    const endCol = Math.min(this.cols - 1, Math.floor(screenRight / this.meterTileSize));
    const startRow = Math.max(0, Math.floor(screenTop / this.meterTileSize));
    const endRow = Math.min(this.rows - 1, Math.floor(screenBottom / this.meterTileSize));

    // 3. Renderujemy tylko widoczne kafelki
    for (let col = startCol; col <= endCol; col++) {
      for (let row = startRow; row <= endRow; row++) {
        const key = this.getTileKey(col, row);
        const img = this.tileCache.get(key);

        // Ustawiamy kafelek we właściwym miejscu w metrach
        const x = col * this.meterTileSize;
        const y = row * this.meterTileSize;

        if (img) {
          // Rysujemy załadowany obrazek używając skalowania
          image(img, x, y, this.meterTileSize, this.meterTileSize);
        } else {
          // Jeśli kafelka nie ma w cache, prosimy o załadowanie
          this.asyncRequestTile(col, row);
          
          // Placeholder dopóki kafelek się nie załaduje (szary kwadrat z cienką ramką)
          push();
          fill(235);
          stroke(210);
          strokeWeight(1 / zoom); // Grubość linii zawsze 1px niezależnie od przybliżenia
          rect(x, y, this.meterTileSize, this.meterTileSize);
          pop();
        }
      }
    }

    // 4. CZYSZCZENIE PAMIĘCI (RAM Guard): Jeśli cache ma > 25 kafelków, usuń niewidoczne
    if (this.tileCache.size > 25) {
      for (const [key, _] of this.tileCache) {
        const [c, r] = key.split('_').map(Number);
        // Jeśli kafelek wypadł z ekranu, wyrzuć go z pamięci
        if (c < startCol || c > endCol || r < startRow || r > endRow) {
          this.tileCache.delete(key);
        }
      }
    }
  }
}

function isCollidingWithLand() {
  // Wektory kierunkowe statku
  let cosH = Math.cos(hdg);
  let sinH = Math.sin(hdg);
  
  // Wektory prostopadłe (dla burt lewej i prawej)
  let cosP = Math.cos(hdg - Math.PI / 2); // Lewa (Port)
  let sinP = Math.sin(hdg - Math.PI / 2);
  let cosS = Math.cos(hdg + Math.PI / 2); // Prawa (Starboard)
  let sinS = Math.sin(hdg + Math.PI / 2);

  // Połowa długości i szerokości w metrach
  let halfL = shipPixL * 0.5; 
  let halfB = shipPixB * 0.5;

  // Definiujemy 6 czujników kolizji (zapisujemy je też globalnie do rysowania)
  window.collisionSensors = [
    { x: posX + halfL * cosH, y: posY + halfL * sinH }, // Dziób (Środek)
    { x: posX - halfL * cosH, y: posY - halfL * sinH }, // Rufa (Środek)
    { x: posX + (halfL*0.8) * cosH + halfB * cosP, y: posY + (halfL*0.8) * sinH + halfB * sinP }, // Lewa Burta (Dziób)
    { x: posX - (halfL*0.8) * cosH + halfB * cosP, y: posY - (halfL*0.8) * sinH + halfB * sinP }, // Lewa Burta (Rufa)
    { x: posX + (halfL*0.8) * cosH + halfB * cosS, y: posY + (halfL*0.8) * sinH + halfB * sinS }, // Prawa Burta (Dziób)
    { x: posX - (halfL*0.8) * cosH + halfB * cosS, y: posY - (halfL*0.8) * sinH + halfB * sinS }  // Prawa Burta (Rufa)
  ];

  // Sprawdzamy każdy punkt na mapie
  for (let pt of window.collisionSensors) {
    if (getMaskValueAt(pt.x, pt.y) > 200) { // Próg lądu
      return true; // Rozbiliśmy się!
    }
  }
  return false;
}

function drawSensors() {
  if (!debugMode) return;

  // 1. RYSOWANIE CZUJNIKÓW (Powiększone i wzmocnione kolory)
  if (window.debugSensors) {
    noStroke();
    for (let pt of window.debugSensors) {
      if (pt.type === 0.0) {
        fill(255, 255, 0); // ŻÓŁTY: Stępka (Squat) - powiększone
        ellipse(pt.x, pt.y, 6, 6);
      } else if (pt.type === 1.0) {
        fill(255, 0, 0); // CZERWONY: Obrys kadłuba (Kolizje)
        ellipse(pt.x, pt.y, 6, 6);
      } else {
        fill(0, 255, 255, 180); // BŁĘKITNY: Promienie Bank Effect
        ellipse(pt.x, pt.y, 3, 3);
      }
    }
  }

  // 2. HUD FIZYCZNY I WEKTORY SIŁ
  if (window.hydroDebug) {
    push();
    // Przenosimy środek rysowania na środek statku
    translate(posX, posY);
    
    // --- WEKTOR SIŁY POPRZECZNEJ (BANK EFFECT) ---
    rotate(hdg); // Obracamy się zgodnie z kursem statku
    
    let forceScale = 0.0001; // Skala siły (aby zmieściła się na ekranie)
    let mappedForce = window.hydroDebug.forceY * forceScale;

    if (Math.abs(mappedForce) > 1.0) {
      stroke(255, 0, 255); // Jaskrawy różowy dla wizualizacji siły
      strokeWeight(3 / zoom);
      
      // Linia siły (wychodzi prostopadle z boku statku)
      line(0, 0, 0, mappedForce);
      
      // Grot strzałki
      fill(255, 0, 255);
      noStroke();
      let arrowDir = mappedForce > 0 ? 1 : -1; // W lewo czy w prawo?
      triangle(-4/zoom, mappedForce - arrowDir*(6/zoom), 
                4/zoom, mappedForce - arrowDir*(6/zoom), 
                0, mappedForce);
      
    }
    
    // --- TEKSTOWY HUD OBOK STATKU ---
    rotate(-hdg); // Odwracamy obrót, by tekst był czytelny poziomo (zawsze do góry)
    
    // Zapobiegamy skalowaniu tekstu przy oddalaniu/przybliżaniu kamery
    let hudScale = constrain(1/zoom, 0.5, 2.0);
    scale(hudScale); 

    fill(255);
    stroke(0); // Czarna obwódka dla czytelności na każdym tle
    strokeWeight(3);
    textSize(14);
    textAlign(LEFT, CENTER);
    
    // Zmieniamy na kN (kiloniutony) i kNm dla czytelności (dzielenie przez 1000)
    let txtSquat = `SQUAT MULTI: ${window.hydroDebug.squat.toFixed(2)}x`;
    let txtBankY = `BANK Y (Spychanie): ${(window.hydroDebug.forceY / 1000).toFixed(1)} kN`;
    let txtBankN = `BANK N (Obrót): ${(window.hydroDebug.forceN / 1000).toFixed(1)} kNm`;
    
    // Rysujemy tekst ok. 80 pikseli w prawo od statku
    text(txtSquat, 80, -25);
    
    // Jeśli działa Bank Effect, podświetlamy tekst na różowo
    if (Math.abs(window.hydroDebug.forceY) > 5000) fill(255, 100, 255);
    else fill(255);
    text(txtBankY, 80, 0);
    text(txtBankN, 80, 25);
    
    pop();
  }
}

function drawMaskRadar() {
  if (!depthMap) return;

  push();
  noStroke(); // Wyłączamy obramowania dla wydajności
  rectMode(CENTER);

  // Skanujemy obszar 400x400 metrów wokół statku w odstępach co 8 metrów
  let scanRange = 500; 
  let step = 20; 

  for (let x = -scanRange; x <= scanRange; x += step) {
    for (let y = -scanRange; y <= scanRange; y += step) {
      
      let worldX = posX + x;
      let worldY = posY + y;

      // Odczyt z maski w danym punkcie świata
      let val = getMaskValueAt(worldX, worldY);

      // Kolorowanie w zależności od odczytanej wartości z maski
      if (val > 200) {
        fill(255, 0, 0, 150);     // CZERWONY: Ląd (kolizja)
      } else if (val > 0) {
        fill(255, 255, 0, 150);   // ŻÓŁTY: Wartości pośrednie (płytka woda/krawędzie)
      } else {
        fill(0, 50, 255, 60);     // NIEBIESKI: Czysta, głęboka woda
      }

      rect(worldX, worldY, step, step);
    }
  }
  pop();
}

// Konfiguracja matrycy hydrodynamicznej statku
const HULL_STATIONS = [
  { xFact: -0.45, wFact: 0.6, pressureWeight:  1.2 }, // Rufa: Max ssanie
  { xFact: -0.20, wFact: 1.0, pressureWeight:  0.8 }, // Obło rufowe: Wspomaganie obrotu
  { xFact:  0.00, wFact: 1.0, pressureWeight:  0.0 }, // Środek: Tylko Squat
  { xFact:  0.30, wFact: 1.0, pressureWeight: -0.5 }, // Barek: Początek Cushion
  { xFact:  0.48, wFact: 0.3, pressureWeight: -1.2 }  // Dziób: Max poduszka
];

// Mnożniki szerokości (B/2): 0.0=Stępka, 1.0=Burta (Kolizja), >1.0=Czujniki Bank Effect
const Y_MULT = [0.0, 1.0, 1.5, 2.5, 4.0];

// Dodane argumenty: u, v, r, pivotX
function scanHydrodynamics(posX, posY, hdg, L, B, draft, u, v, r, pivotX) {
  let cosH = Math.cos(hdg);
  let sinH = Math.sin(hdg);
  
  let result = {
    isColliding: false,
    squatFactor: 0, 
    bankY: 0,       
    bankN: 0        
  };

  window.debugSensors = []; 
  let totalSquat = 0;

  for (let station of HULL_STATIONS) {
    let localX = station.xFact * L;
    let localHalfB = (B * 0.5) * station.wFact;

    let suctionPort = 0;
    let suctionStbd = 0;

    // PROBLEM 1 & 2: Local Inflow Dependency & Directional Shielding
    // localVy określa, jak mocno woda omywa daną sekcję w poprzek
    let localVy = v + r * localX; 
    
    // Baza 1.0 (czyste ssanie z u) + wpływ poprzecznego przepływu.
    // Daje to drastyczny wzrost ssania na rufie podczas mocnego wychylenia (yaw).
    let inflowMultiplier = 1.0 + Math.abs(localVy) * 0.1; 

    // Shielding: Zjawiska hydrodynamiczne słabną na samych krańcach z powodu ucieczki ciśnienia
    let shielding = 1.0 - Math.abs(station.xFact) * 0.3;

    for (let i = 0; i < Y_MULT.length; i++) {
      let yMultVal = Y_MULT[i];
      let yOffset;

      if (yMultVal <= 1.0) {
        yOffset = localHalfB * yMultVal;
      } else {
        let wakeExpansion = (station.xFact < 0) ? 1.2 : 1.0; 
        yOffset = (B * 0.5) * yMultVal * wakeExpansion;
      }

      let wx_port = posX + localX * cosH - (-yOffset) * sinH;
      let wy_port = posY + localX * sinH + (-yOffset) * cosH;
      let wx_stbd = posX + localX * cosH - (yOffset) * sinH;
      let wy_stbd = posY + localX * sinH + (yOffset) * cosH;

      let valPort = getMaskValueAt(wx_port, wy_port);
      let valStbd = getMaskValueAt(wx_stbd, wy_stbd);
      
      let depthPort = decodeDepth(valPort);
      let depthStbd = decodeDepth(valStbd);

      if (debugMode) {
        window.debugSensors.push({ x: wx_port, y: wy_port, type: yMultVal });
        if (yOffset > 0) window.debugSensors.push({ x: wx_stbd, y: wy_stbd, type: yMultVal });
      }

      if (yMultVal === 0.0) {
        if (valPort === 255 || depthPort < draft) result.isColliding = true;
        if (depthPort < draft * 4.0) {
          let depthRatio = draft / Math.max(depthPort, draft + 0.1);
          totalSquat += Math.pow(depthRatio, 2); 
        }
      }
      else if (yMultVal === 1.0) {
        if (valPort === 255 || depthPort < draft) result.isColliding = true;
        if (valStbd === 255 || depthStbd < draft) result.isColliding = true;
      }
      else {
        let distanceWeight = 1.0 / Math.pow(yMultVal, 2); 

        // Aplikacja Inflow i Shielding do sił ssania
        let effectPort = Math.pow(draft / Math.max(depthPort, draft + 0.1), 1.5) * distanceWeight * inflowMultiplier * shielding;
        let effectStbd = Math.pow(draft / Math.max(depthStbd, draft + 0.1), 1.5) * distanceWeight * inflowMultiplier * shielding;

        suctionPort += effectPort;
        suctionStbd += effectStbd;
      }
    }

    let asymmetry = suctionStbd - suctionPort;
    let sectionY = asymmetry * station.pressureWeight;

    // PROBLEM 5: Pivot Point Coupling
    // Zamiast kręcić statkiem geometrycznie, siła działa na dynamiczne ramię względem Pivot Point
    let currentPivotX = pivotX !== null ? pivotX : 0;
    let dynamicLeverArm = localX - currentPivotX;

    result.bankY += sectionY;
    result.bankN += sectionY * dynamicLeverArm; 
  }

  result.squatFactor = totalSquat / HULL_STATIONS.length;
  return result;
}

// Funkcja zamieniająca kolor z maski na metry (zgodnie z Twoją specyfikacją)
function decodeDepth(val) {
  if (val === 255) return 0.0;   // Ląd
  if (val === 0) return 50.0;    // Głęboka woda (brak limitów)
  if (val >= 200) return 2.0;    // Boje (sztuczne płytkowodzie, by je ominąć)
  
  // Woda płytka (wartości z Twojej maski 80 - 189)
  if (val >= 80 && val <= 189) {
    return 0.25 + ((189 - val) / (189 - 80)) * 9.5; 
  }
  // Woda głębsza (1 - 79)
  return 10.0 + ((79 - val) / 79) * 40.0;
}

async function loadGzipMask(url) {
  try {
    const response = await fetch(url);
    if (!response.ok) throw new Error(`Błąd pobierania: ${response.status}`);

    // Przekierowanie pobieranego strumienia przez wbudowany dekompresor GZIP
    const decompressedStream = response.body.pipeThrough(
      new DecompressionStream("gzip")
    );

    // Zamiana rozpakowanego strumienia na końcowy ArrayBuffer
    const buffer = await new Response(decompressedStream).arrayBuffer();

    isMaskReady = true;

    // Gotowa, surowa i ultraszybka tablica 140 MB w RAMIE
    depthMap = new Uint8Array(buffer);
    
    console.log("Maska została pomyślnie rozpakowana w locie do RAM!");
  } catch (error) {
    console.error("Problem z ładowaniem maski:", error);
  }
}