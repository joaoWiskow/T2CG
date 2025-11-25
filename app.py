# OpenGLBasico3D-V5-50x50-final.py
# Labirinto 50x50 com corredores e "meio-fio" nas bordas
# Autor: adaptado por ChatGPT

import sys
import time
import random as ALE
from math import sin, cos, radians, sqrt
import heapq

from OpenGL.GL import *
from OpenGL.GLUT import *
from OpenGL.GLU import *

# -------------------- configurações do mapa (ajuste fácil)
MAP_SIZE = 50        # 50 x 50
WALL_PROB = 0.06     # probabilidade inicial de parede interna
NUM_CORRIDORS = 120  # quantas escavações/corredores para "conjeturar caminhos"

# -------------------- utilidades mínimas
class Ponto:
    def __init__(self, x=0.0, y=0.0, z=0.0):
        self.x = float(x)
        self.y = float(y)
        self.z = float(z)
    def imprime(self, label=""):
        print(label, f"({self.x:.2f},{self.y:.2f},{self.z:.2f})")

# cores
White = (1.0,1.0,1.0)
Black = (0.0,0.0,0.0)
Red = (1.0,0.0,0.0)
Green = (0.0,1.0,0.0)
Blue = (0.0,0.0,1.0)
Yellow = (1.0,1.0,0.0)

# tons marrons
BrownFloor = (0.45,0.25,0.07)
BrownWall = (0.36,0.25,0.20)
Wood = (0.6,0.3,0.2)

# cores configuráveis
PlayerColor = Blue
EnemyColor  = Red
EnergyColor = Yellow
FloorColor  = BrownFloor
WallColor   = BrownWall

def defineCor(c):
    glColor3f(c[0], c[1], c[2])

# -------------------- constantes do mundo
ALTURA_PAREDE = 2.7
ESPESSURA_PAREDE = 0.25
ALTURA_PORTA = 2.10
ALTURA_JANELA_BASE = 0.9

# tipos de célula
CELL_EMPTY = 0
CELL_WALL_H = 1
CELL_WALL_V = 2
CELL_PLAYER = 'P'
CELL_FIXED = 'F'
CELL_WINDOW = 'J'
CELL_DOOR = 'D'

MAX_DIM = 400

# velocidades
PLAYER_SPEED = 10.0
ENEMY_SPEED = 3.5

# pathfinding
PATH_RECALC_INTERVAL = 0.9

# mínimos requisitados
MIN_FIXED_OBJECTS = 10
MIN_ENEMIES = 10
MIN_ENERGIES = 10

# -------------------- estado global
Cidade = []
QtdX = 0
QtdZ = 0

Observador = Ponto()
Alvo = Ponto()
TerceiraPessoa = Ponto()
PosicaoVeiculo = Ponto()

modo_primeira_pessoa = True
modo_terceira_focar_centro = True

# -------------------- entidades
class Player:
    def __init__(self, x=0.5, z=0.5):
        self.x = x
        self.z = z
        self.y = 0.0
        self.angle = 0.0
        self.moving = False
        self.energy = 100.0
        self.score = 0
    def forward_vector(self):
        a = radians(self.angle)
        return cos(a), -sin(a)

player = Player()

class Enemy:
    def __init__(self, x,z):
        self.x = x
        self.z = z
        self.y = 0.0
        self.color = EnemyColor
        self.path = []
        self.path_idx = 0
        self.recalc_timer = 0.0
    def pos(self):
        return (self.x,self.z)

# fixed objects: {'x':int,'z':int,'type':str}
fixed_objects = []
enemies = []
energies = []
mapa_janelas = {}

# timers
oldTime = time.time()
GlobalTime = 0.0

# -------------------- util helpers
def hsv_to_rgb(h, s, v):
    i = int(h*6.0)
    f = (h*6.0) - i
    p = v * (1.0 - s)
    q = v * (1.0 - f*s)
    t = v * (1.0 - (1.0 - f) * s)
    i = i % 6
    if i == 0: r,g,b = v,t,p
    elif i == 1: r,g,b = q,v,p
    elif i == 2: r,g,b = p,v,t
    elif i == 3: r,g,b = p,q,v
    elif i == 4: r,g,b = t,p,v
    else: r,g,b = v,p,q
    return (r,g,b)

# -------------------- geração do mapa com borda "meio-fio" e corridors adicionais
def generate_sparse_map_with_corridors(size=MAP_SIZE, wall_prob=WALL_PROB, n_corridors=NUM_CORRIDORS):
    mat = [[1 for _ in range(size)] for __ in range(size)]
    for z in range(1, size-1):
        for x in range(1, size-1):
            mat[z][x] = 1 if (ALE.random() < wall_prob and ALE.random() < 0.9) else 0
    # bordas coerentes (meio-fio)
    for x in range(size):
        mat[0][x] = CELL_WALL_H
        mat[size-1][x] = CELL_WALL_H
    for z in range(size):
        mat[z][0] = CELL_WALL_V
        mat[z][size-1] = CELL_WALL_V
    # jogador no centro preferencialmente
    center = size//2
    if mat[center][center] != 0:
        found = False
        for r in range(1, size//2):
            for dz in range(-r, r+1):
                for dx in range(-r, r+1):
                    x = center + dx
                    z = center + dz
                    if 0 <= x < size and 0 <= z < size and mat[z][x] == 0:
                        mat[z][x] = 'P'
                        found = True
                        break
                if found: break
            if found: break
        if not found:
            mat[center][center] = 'P'
    else:
        mat[center][center] = 'P'
    # cavar corredores
    free_cells = [(x,z) for z in range(1,size-1) for x in range(1,size-1) if mat[z][x] == 0 or mat[z][x] == 'P']
    if len(free_cells) < 2:
        for z in range(1,size-1):
            for x in range(1,size-1):
                if ALE.random() < 0.02:
                    mat[z][x] = 0
        free_cells = [(x,z) for z in range(1,size-1) for x in range(1,size-1) if mat[z][x] == 0 or mat[z][x] == 'P']
    def carve_path(a,b):
        x,y = a
        tx,ty = b
        attempts = 0
        while (x,y) != (tx,ty) and attempts < (abs(tx-x)+abs(ty-y))*4 + 50:
            attempts += 1
            mat[y][x] = 0
            dx = tx - x
            dy = ty - y
            if dx != 0 and dy != 0:
                if ALE.random() < 0.6:
                    x += 1 if dx>0 else -1
                else:
                    y += 1 if dy>0 else -1
            elif dx != 0:
                x += 1 if dx>0 else -1
            elif dy != 0:
                y += 1 if dy>0 else -1
            mat[y][x] = 0
    if free_cells:
        for i in range(n_corridors):
            a = ALE.choice(free_cells)
            b = ALE.choice(free_cells)
            if a != b:
                carve_path(a,b)
    # orientar paredes residuais
    for z in range(1,size-1):
        for x in range(1,size-1):
            if mat[z][x] != 0 and mat[z][x] != 'P':
                up = (0 <= z-1 < size and mat[z-1][x] == 0)
                down = (0 <= z+1 < size and mat[z+1][x] == 0)
                left = (0 <= x-1 < size and mat[z][x-1] == 0)
                right = (0 <= x+1 < size and mat[z][x+1] == 0)
                if (left or right) and not (up or down):
                    mat[z][x] = CELL_WALL_V
                elif (up or down) and not (left or right):
                    mat[z][x] = CELL_WALL_H
                else:
                    mat[z][x] = CELL_WALL_H if ALE.random() < 0.5 else CELL_WALL_V
    return mat

# -------------------- geração direta (gera sempre — sem checar arquivo)
def generate_and_setup_map():
    global Cidade, QtdX, QtdZ
    Cidade = generate_sparse_map_with_corridors(MAP_SIZE, WALL_PROB, NUM_CORRIDORS)
    QtdZ = len(Cidade)
    QtdX = len(Cidade[0])
    rebuild_fixed_and_windows_from_map()
    print(f"Mapa gerado automaticamente: {QtdX}x{QtdZ} ({QtdX*QtdZ} m^2) — WALL_PROB={WALL_PROB}, CORRIDORS={NUM_CORRIDORS}")

def rebuild_fixed_and_windows_from_map():
    global fixed_objects, mapa_janelas
    fixed_objects = []
    mapa_janelas = {}
    for z in range(QtdZ):
        for x in range(QtdX):
            v = Cidade[z][x]
            if v == CELL_FIXED or v == 'F':
                typ = ALE.choice(['chair','table','vase'])
                fixed_objects.append({'x':x,'z':z,'type':typ})
            if v == CELL_WINDOW or v == 'J':
                mapa_janelas[(z,x)] = 1.0
            if v == CELL_PLAYER or v == 'P':
                player.x = x+0.5
                player.z = z+0.5

def ensure_min_fixed_objects(n=MIN_FIXED_OBJECTS):
    current = sum(1 for z in range(QtdZ) for x in range(QtdX) if Cidade[z][x] == CELL_FIXED or Cidade[z][x] == 'F')
    need = max(0, n - current)
    if need == 0:
        return
    free = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z) and not (Cidade[z][x] == CELL_PLAYER or Cidade[z][x] == 'P')]
    ALE.shuffle(free)
    added = 0
    while need > 0 and free:
        x,z = free.pop()
        Cidade[z][x] = 'F'
        need -= 1
        added += 1
    rebuild_fixed_and_windows_from_map()
    print(f"Objetos fixos adicionados: {added}")

# -------------------- desenho
def DesenhaLadrilho(x=None, z=None):
    if x is not None and z is not None:
        f1 = FloorColor
        f2 = (min(1.0, f1[0]+0.08), min(1.0, f1[1]+0.06), min(1.0, f1[2]+0.04))
        use = f1 if ((x + z) % 2 == 0) else f2
        glColor3f(*use)
    else:
        glColor3f(*FloorColor)
    glBegin(GL_QUADS)
    glNormal3f(0,1,0)
    glVertex3f(-0.5,0,-0.5)
    glVertex3f(-0.5,0,0.5)
    glVertex3f(0.5,0,0.5)
    glVertex3f(0.5,0,-0.5)
    glEnd()

def DesenhaParedeHorizontal():
    glColor3f(*WallColor)
    glPushMatrix()
    glTranslatef(0, ALTURA_PAREDE/2.0, 0)
    glScalef(1.0, ALTURA_PAREDE, ESPESSURA_PAREDE)
    glutSolidCube(1)
    glPopMatrix()

def DesenhaParedeVertical():
    glColor3f(*WallColor)
    glPushMatrix()
    glTranslatef(0, ALTURA_PAREDE/2.0, 0)
    glScalef(ESPESSURA_PAREDE, ALTURA_PAREDE, 1.0)
    glutSolidCube(1)
    glPopMatrix()

def DesenhaPorta():
    glColor3f(0.45,0.25,0.1)
    glPushMatrix()
    glTranslatef(0, ALTURA_PORTA/2.0, 0)
    glScalef(0.9, ALTURA_PORTA, 0.05)
    glutSolidCube(1)
    glPopMatrix()

def DesenhaJanela(altura):
    glColor3f(0.7,0.85,0.95)
    glPushMatrix()
    glTranslatef(0, ALTURA_JANELA_BASE + altura/2.0, 0)
    glScalef(0.9, altura, 0.05)
    glutSolidCube(1)
    glPopMatrix()

def DesenhaHumano():
    glPushMatrix()
    glScalef(0.4,0.7,0.25)
    glutSolidCube(1)
    glPopMatrix()
    glPushMatrix()
    glTranslatef(0,0.7+0.25,0)
    glutSolidSphere(0.25,12,12)
    glPopMatrix()
    glPushMatrix()
    glTranslatef(-0.15,-0.7,0)
    glScalef(0.15,0.5,0.15)
    glutSolidCube(1)
    glPopMatrix()
    glPushMatrix()
    glTranslatef(0.15,-0.7,0)
    glScalef(0.15,0.5,0.15)
    glutSolidCube(1)
    glPopMatrix()

def DesenhaInimigo():
    glutSolidSphere(0.3,12,12)

def DesenhaEnergia():
    glPushMatrix()
    glutSolidSphere(0.2,10,10)
    glPopMatrix()

def DesenhaObjetoFixoTipo(obj):
    typ = obj.get('type','chair')
    if typ == 'chair':
        glPushMatrix()
        glTranslatef(0,0.15,0)
        glScalef(0.4,0.3,0.4)
        glutSolidCube(1)
        glPopMatrix()
        glPushMatrix()
        glTranslatef(0,0.45,-0.12)
        glScalef(0.4,0.5,0.08)
        glutSolidCube(1)
        glPopMatrix()
    elif typ == 'table':
        glPushMatrix()
        glTranslatef(0,0.28,0)
        glScalef(0.7,0.12,0.7)
        glutSolidCube(1)
        glPopMatrix()
        glPushMatrix()
        glTranslatef(0,0.08,0)
        glScalef(0.08,0.36,0.08)
        glutSolidCube(1)
        glPopMatrix()
    else:
        glPushMatrix()
        glTranslatef(0,0.25,0)
        glutSolidSphere(0.18,10,10)
        glPopMatrix()
        glPushMatrix()
        glTranslatef(0,0.45,0)
        glScalef(0.12,0.25,0.12)
        glutSolidCube(1)
        glPopMatrix()

def DesenhaCidade():
    for z in range(QtdZ):
        for x in range(QtdX):
            glPushMatrix()
            glTranslatef(x, 0, z)
            DesenhaLadrilho(x,z)
            cell = Cidade[z][x]
            if cell == CELL_WALL_H or cell == 1:
                DesenhaParedeHorizontal()
            elif cell == CELL_WALL_V or cell == 2:
                DesenhaParedeVertical()
            elif cell == CELL_DOOR or cell == 'D':
                DesenhaPorta()
            elif cell == CELL_WINDOW or cell == 'J':
                h = mapa_janelas.get((z,x),1.0)
                DesenhaJanela(h)
            elif cell == CELL_FIXED or cell == 'F':
                glPushMatrix()
                glTranslatef(0,0,0)
                glColor3f(*Wood)
                for obj in fixed_objects:
                    if obj['x'] == x and obj['z'] == z:
                        DesenhaObjetoFixoTipo(obj)
                        break
                glPopMatrix()
            glPopMatrix()

# -------------------- navegação / pathfinding
def is_cell_walkable(x,z):
    if x < 0 or z < 0 or x >= QtdX or z >= QtdZ:
        return False
    v = Cidade[z][x]
    if v == 0 or v == CELL_PLAYER or v == 'P':
        return True
    return False

def neighbors_of(cell):
    x,z = cell
    nbrs = [(x+1,z),(x-1,z),(x,z+1),(x,z-1)]
    valid = [(nx,nz) for (nx,nz) in nbrs if 0 <= nx < QtdX and 0 <= nz < QtdZ and is_cell_walkable(nx,nz)]
    return valid

def heuristic(a,b):
    return abs(a[0]-b[0]) + abs(a[1]-b[1])

def a_star(start, goal):
    if start == goal:
        return [start]
    open_set = []
    heapq.heappush(open_set, (0, start))
    came_from = {}
    gscore = {start: 0}
    fscore = {start: heuristic(start, goal)}
    visited = set()
    while open_set:
        _, current = heapq.heappop(open_set)
        if current == goal:
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            path.reverse()
            return path
        visited.add(current)
        for nb in neighbors_of(current):
            tentative_g = gscore[current] + 1
            if nb in visited and tentative_g >= gscore.get(nb, 1e9):
                continue
            if tentative_g < gscore.get(nb, 1e9):
                came_from[nb] = current
                gscore[nb] = tentative_g
                f = tentative_g + heuristic(nb, goal)
                fscore[nb] = f
                heapq.heappush(open_set, (f, nb))
    return None

# -------------------- spawn entidades garantindo mínimos
def spawn_random_entities(min_enemies=MIN_ENEMIES, min_energies=MIN_ENERGIES):
    enemies.clear()
    energies.clear()
    free_cells = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z) and not (abs(x+0.5-player.x)<0.1 and abs(z+0.5-player.z)<0.1)]
    ALE.shuffle(free_cells)
    for i in range(min_enemies):
        if not free_cells:
            break
        x,z = free_cells.pop()
        e = Enemy(x+0.5, z+0.5)
        e.color = hsv_to_rgb(ALE.random(), 0.85, 0.9)
        e.path = []
        e.path_idx = 0
        e.recalc_timer = ALE.random()*PATH_RECALC_INTERVAL
        enemies.append(e)
    free_cells = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z) and not any(int(en.x)==x and int(en.z)==z for en in enemies)]
    ALE.shuffle(free_cells)
    for i in range(min_energies):
        if not free_cells:
            break
        x,z = free_cells.pop()
        energies.append([x+0.5, z+0.5])
    # garantir ao menos os mínimos
    if len(fixed_objects) < MIN_FIXED_OBJECTS:
        ensure_min_fixed_objects(MIN_FIXED_OBJECTS)
    print(f"Spawn final: enemies={len(enemies)}, energies={len(energies)}, fixed={len(fixed_objects)}")

# -------------------- simulação / movimento
def step_simulation(dt):
    if player.moving and player.energy > 0:
        vx, vz = player.forward_vector()
        nx = player.x + vx * PLAYER_SPEED * dt
        nz = player.z + vz * PLAYER_SPEED * dt
        if not collides_with_wall(nx, nz):
            player.x = nx
            player.z = nz
            player.energy -= PLAYER_SPEED * dt * 0.5
            if player.energy < 0: player.energy = 0
        else:
            player.moving = False

    for e in enemies:
        e.recalc_timer -= dt
        ex_cell = (int(e.x), int(e.z))
        pl_cell = (int(player.x), int(player.z))
        need_recalc = False
        if e.recalc_timer <= 0.0 or not e.path or e.path_idx >= len(e.path) or (e.path and e.path[-1] != pl_cell):
            need_recalc = True
        if need_recalc:
            e.recalc_timer = PATH_RECALC_INTERVAL
            path = a_star(ex_cell, pl_cell)
            if path:
                e.path = path
                if len(path) > 1 and ex_cell == path[0]:
                    e.path_idx = 1
                else:
                    e.path_idx = 1 if len(path) > 1 else 0
            else:
                e.path = []
                e.path_idx = 0
        if e.path and e.path_idx < len(e.path):
            target_cell = e.path[e.path_idx]
            tx = target_cell[0] + 0.5
            tz = target_cell[1] + 0.5
            dx = tx - e.x
            dz = tz - e.z
            dist = sqrt(dx*dx + dz*dz)
            if dist < 0.05:
                e.path_idx += 1
            else:
                vx = dx / dist
                vz = dz / dist
                nx = e.x + vx * ENEMY_SPEED * dt
                nz = e.z + vz * ENEMY_SPEED * dt
                if collides_with_wall(nx, nz):
                    e.recalc_timer = 0.0
                else:
                    e.x = nx
                    e.z = nz
        else:
            if ALE.random() < 0.01:
                free = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z)]
                if free:
                    fx,fz = ALE.choice(free)
                    e.x = fx + 0.5
                    e.z = fz + 0.5

    for e in enemies:
        if distance(player.x, player.z, e.x, e.z) < 0.6:
            player.score -= 10
            move_entity_to_free_cell(e)

    for cap in energies:
        if distance(player.x, player.z, cap[0], cap[1]) < 0.6:
            player.energy = min(100.0, player.energy + 50.0)
            player.score += 5
            move_capsule_to_free_cell(cap)

def distance(x1,z1,x2,z2):
    return sqrt((x1-x2)**2 + (z1-z2)**2)

def move_entity_to_free_cell(e):
    free = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z) and distance(x+0.5,z+0.5,player.x,player.z)>2.0]
    if not free: return
    x,z = ALE.choice(free)
    e.x = x+0.5
    e.z = z+0.5
    e.path = []
    e.path_idx = 0
    e.recalc_timer = PATH_RECALC_INTERVAL

def move_capsule_to_free_cell(cap):
    free = [(x,z) for z in range(QtdZ) for x in range(QtdX) if is_cell_walkable(x,z)]
    if not free: return
    x,z = ALE.choice(free)
    cap[0] = x+0.5
    cap[1] = z+0.5

def collides_with_wall(cx, cz):
    ix = int(cx)
    iz = int(cz)
    if ix < 0 or iz < 0 or ix >= QtdX or iz >= QtdZ:
        return True
    cell = Cidade[iz][ix]
    if cell == 0 or cell == CELL_PLAYER or cell == 'P':
        return False
    if cell == CELL_DOOR or cell == 'D':
        return False
    return True

# -------------------- OpenGL: luz, câmera, display
Angulo = 0.0
AlturaViewportDeMensagens = 0.18
AnguloDeVisao = 60.0
AspectRatio = 1.0

def DefineLuz():
    glEnable(GL_LIGHTING)
    glEnable(GL_LIGHT0)
    amb = [0.3,0.3,0.3,1.0]
    dif = [0.7,0.7,0.7,1.0]
    spec = [1.0,1.0,1.0,1.0]
    pos0 = [player.x, 5.0, player.z, 1.0]
    glLightfv(GL_LIGHT0, GL_AMBIENT, amb)
    glLightfv(GL_LIGHT0, GL_DIFFUSE, dif)
    glLightfv(GL_LIGHT0, GL_SPECULAR, spec)
    glLightfv(GL_LIGHT0, GL_POSITION, pos0)
    if QtdX > 0 and QtdZ > 0:
        glEnable(GL_LIGHT1)
        l_amb = [0.05,0.02,0.06,1.0]
        pulse = 0.6 + 0.4 * 0.5 * (1.0 + sin(GlobalTime * 1.5))
        l_diff = [0.6*pulse,0.2*pulse,0.8*pulse,1.0]
        l_pos = [QtdX/2.0, max(QtdX,QtdZ)*0.6, QtdZ/2.0, 1.0]
        glLightfv(GL_LIGHT1, GL_AMBIENT, l_amb)
        glLightfv(GL_LIGHT1, GL_DIFFUSE, l_diff)
        glLightfv(GL_LIGHT1, GL_POSITION, l_pos)

def PosicUser():
    w = glutGet(GLUT_WINDOW_WIDTH)
    h = glutGet(GLUT_WINDOW_HEIGHT)
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    global AspectRatio
    AspectRatio = w/h if h!=0 else 1
    gluPerspective(AnguloDeVisao, AspectRatio, 0.01, 2000)
    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()
    if modo_primeira_pessoa:
        a = radians(player.angle)
        dx = cos(a)
        dz = -sin(a)
        eye_x = player.x
        eye_y = 1.5
        eye_z = player.z
        center_x = eye_x + dx
        center_y = 1.5
        center_z = eye_z + dz
        gluLookAt(eye_x, eye_y, eye_z, center_x, center_y, center_z, 0,1,0)
    else:
        camY = max(QtdX,QtdZ) * 1.5
        camX = QtdX/2.0
        camZ = QtdZ/2.0
        if modo_terceira_focar_centro:
            tgtX = QtdX/2.0
            tgtZ = QtdZ/2.0
        else:
            tgtX = player.x
            tgtZ = player.z
        gluLookAt(camX, camY, camZ, tgtX, 0, tgtZ, 0,0,-1)

def DesenhaEm2D():
    ativar_luz = False
    if glIsEnabled(GL_LIGHTING):
        glDisable(GL_LIGHTING)
        ativar_luz = True
    w = glutGet(GLUT_WINDOW_WIDTH)
    h = glutGet(GLUT_WINDOW_HEIGHT)
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    glViewport(0, 0, w, int(h*AlturaViewportDeMensagens))
    glOrtho(0,10,0,10,-1,1)
    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()
    defineCor(White)
    PrintString(f"Energia: {player.energy:.0f}  Score: {player.score}", 0.2, 8.0, White)
    PrintString(f"Modo: {'1P' if modo_primeira_pessoa else '3P'}  Movimento: {'ON' if player.moving else 'OFF'}", 0.2, 6.5, White)
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()
    glViewport(0, int(h*AlturaViewportDeMensagens), w, int(h - h*AlturaViewportDeMensagens))
    if ativar_luz:
        glEnable(GL_LIGHTING)

def PrintString(S, x, y, cor):
    defineCor(cor)
    glRasterPos2f(x,y)
    for c in S:
        glutBitmapCharacter(GLUT_BITMAP_HELVETICA_12, ord(c))

def display():
    global Angulo
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
    DefineLuz()
    PosicUser()
    glMatrixMode(GL_MODELVIEW)
    DesenhaCidade()
    if not modo_primeira_pessoa:
        glPushMatrix()
        glTranslatef(player.x, 0, player.z)
        glRotatef(-player.angle+90, 0,1,0)
        glColor3f(*PlayerColor)
        DesenhaHumano()
        glPopMatrix()
    for e in enemies:
        glPushMatrix()
        glColor3f(*getattr(e,'color', EnemyColor))
        glTranslatef(e.x, 0.3, e.z)
        DesenhaInimigo()
        glPopMatrix()
    for i, cap in enumerate(energies):
        pulse = 0.6 + 0.4 * 0.5 * (1.0 + sin(GlobalTime*5.0 + i))
        ec = (EnergyColor[0]*pulse, EnergyColor[1]*pulse, EnergyColor[2]*pulse)
        scale = 0.9 + 0.15 * (0.5 * (1.0 + sin(GlobalTime*6.0 + i)))
        glPushMatrix()
        glTranslatef(cap[0], 0.2, cap[1])
        glScalef(scale, scale, scale)
        glColor3f(*ec)
        DesenhaEnergia()
        glPopMatrix()
    DesenhaEm2D()
    glutSwapBuffers()

# -------------------- loop e tempo
nFrames = 0
AccumDeltaT = 0

def animate():
    global oldTime, AccumDeltaT, GlobalTime
    now = time.time()
    dt = now - oldTime
    oldTime = now
    AccumDeltaT += dt
    GlobalTime += dt
    step_simulation(dt)
    glutPostRedisplay()

# -------------------- input
ESCAPE = b'\x1b'

def move_forward_step(step=0.5):
    vx, vz = player.forward_vector()
    nx = player.x + vx * step
    nz = player.z + vz * step
    if not collides_with_wall(nx, nz):
        player.x = nx
        player.z = nz

def keyboard(key, x, y):
    global modo_primeira_pessoa, modo_terceira_focar_centro
    if key == ESCAPE:
        os._exit(0)
    if key == b' ':
        player.moving = not player.moving
    if key == b'v' or key == b'V':
        modo_primeira_pessoa = not modo_primeira_pessoa
    if key == b'c' or key == b'C':
        modo_terceira_focar_centro = not modo_terceira_focar_centro
    if key == b'w' or key == b'W':
        move_forward_step(step=0.5)
    if key == b'e' or key == b'E':
        player.energy = 100.0
    glutPostRedisplay()

def arrow_keys(a_keys, x, y):
    if a_keys == GLUT_KEY_LEFT:
        player.angle += 5.0
    if a_keys == GLUT_KEY_RIGHT:
        player.angle -= 5.0
    glutPostRedisplay()

def initialize_opengl():
    glClearColor(0.2,0.5,0.8,1.0)
    glEnable(GL_DEPTH_TEST)
    glShadeModel(GL_SMOOTH)
    glEnable(GL_NORMALIZE)
    glEnable(GL_COLOR_MATERIAL)
    glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE)
    glEnable(GL_LIGHTING)
    glEnable(GL_LIGHT0)

# -------------------- main
def main():
    global QtdX, QtdZ, Cidade
    # gera mapa sempre (sem tentar carregar arquivo)
    generate_and_setup_map()
    ensure_min_fixed_objects(MIN_FIXED_OBJECTS)
    spawn_random_entities(MIN_ENEMIES, MIN_ENERGIES)
    TerceiraPessoa.x = QtdX/2.0
    TerceiraPessoa.y = 10
    TerceiraPessoa.z = QtdZ/2.0
    PosicaoVeiculo.x = QtdX/2.0
    PosicaoVeiculo.y = 0
    PosicaoVeiculo.z = QtdZ/2.0

    glutInit(sys.argv)
    glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE | GLUT_DEPTH)
    glutInitWindowSize(1000,800)
    title = "Labirinto - 50x50 com corredores - meio-fio nas bordas"
    if isinstance(title, str):
        title = title.encode('utf-8')
    glutCreateWindow(title)

    initialize_opengl()
    glutDisplayFunc(display)
    glutIdleFunc(animate)
    glutKeyboardFunc(keyboard)
    glutSpecialFunc(arrow_keys)
    glutMainLoop()

# helper compatibilidade (usa Cidade já setada)
def CarregaLabirintoFromMatrix(mat):
    global Cidade, QtdX, QtdZ
    Cidade = mat
    QtdZ = len(Cidade)
    QtdX = len(Cidade[0])
    rebuild_fixed_and_windows_from_map()

if __name__ == '__main__':
    main()
