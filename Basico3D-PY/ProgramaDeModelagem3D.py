import sys
import math
import random
import time

from OpenGL.GL import *
from OpenGL.GLUT import *
from OpenGL.GLU import *

from Poligono import Poligono
from Ponto import Ponto
from ListaDeCoresRGB import *

# Variáveis globais
AspectRatio = 1.0
angulo = 0

# Controle do modo de projecao
# 0: Projecao Paralela Ortografica; 1: Projecao Perspectiva
# A funcao "PosicUser" utiliza esta variavel. O valor dela eh alterado
# pela tecla 'p'
ModoDeProjecao = 1  # 0: Orthogonal, 1: Perspectiva

# Controle do modo de projecao
# 0: Wireframe; 1: Faces preenchidas
# A funcao "Init" utiliza esta variavel. O valor dela eh alterado
# pela tecla 'e'
ModoDeExibicao = 1  # 0: Wireframe, 1: Faces preenchidas

nFrames = 0
TempoTotal = 0
CantoEsquerdo = (-20, -1, -10)


PontoClicado = None
FoiClicado = False

Base = None
Objeto3D = []
Geratrizes = []

# ********************************************************
#
# ********************************************************
def CriaObjetoPorRotacao(gerador: Poligono, eixoDeRotacao):
    pass


# ********************************************************
#
# ********************************************************
def CriaObjetoPorExtrusao(Gerador: Poligono, Geratriz: Ponto):
    global Objeto3D
    
    Objeto3D.append(Gerador)
    NovaFace = Poligono()

    for idx, v in enumerate(Gerador.Vertices):
        P = Ponto(v.x + Geratriz.x, v.y + Geratriz.y, v.z + Geratriz.z)
        NovaFace.insereVertice(P)

    Objeto3D.append(NovaFace)


# ********************************************************
#
# ********************************************************
def CriaObjetoPorExtrusaoMultipla(Gerador: Poligono):
    for v in Geratrizes:
        v.imprime()


# ********************************************************
#
# ********************************************************
def DesenhaObjeto3D():
    defineCor(Red)
    glLineWidth(3)

    #print(f"===> {len(Objeto3D)}")

    for obj in Objeto3D:
        #for idx, v in enumerate(obj.Vertices):
        #    print(f"    {v.x} {v.y} {v.z}")
            
        defineCor(Orange)
        obj.pintaPoligono()
        defineCor(White)
        obj.desenhaPoligono()

# **********************************************************************
#  Inicializa os parametros globais de OpenGL
# **********************************************************************
def init():
    glClearColor(1.0, 1.0, 0.0, 1.0)  # Fundo de tela amarelo
    glClearDepth(1.0)
    glDepthFunc(GL_LESS)
    glEnable(GL_DEPTH_TEST)
    glEnable(GL_CULL_FACE)
    glEnable(GL_NORMALIZE)
    glShadeModel(GL_SMOOTH)
    
    if ModoDeExibicao:  # Faces Preenchidas??
        glPolygonMode(GL_FRONT_AND_BACK, GL_FILL)
    else:
        glPolygonMode(GL_FRONT_AND_BACK, GL_LINE)

    Base = Poligono()
    Base.LePoligono3D("PoligonoDaBase.txt")

    CriaObjetoPorExtrusao(Base, Ponto(0, 1.5, 0))

    # Cria uma sequencia de geratrizes, para cria um "cano"
    Geratrizes = [Ponto(0, 1.5, 0), Ponto(1, 1.5, 0), Ponto(0, 1.5, 0)]

# ********************************************************
#
# ********************************************************
def animate():
    global angulo, nFrames, TempoTotal
    # TempoTotal += 1
    # nFrames += 1
    # if TempoTotal > 5.0:
    #     print(f"Tempo Acumulado: {TempoTotal} segundos.")
    #     print(f"FPS: {nFrames / TempoTotal}")
    #     TempoTotal = 0
    #     nFrames = 0

    angulo += 1
    glutPostRedisplay()

# **********************************************************************
# Desenha uma c�lula do piso.
# Eh possivel definir a cor da borda e do interior do piso
# O ladrilho tem largula 1, centro no (0,0,0) e est� sobre o plano XZ
# **********************************************************************
def DesenhaLadrilho(corBorda, corDentro):
    defineCor(corDentro)  # Desenha QUAD preenchido
    glBegin(GL_QUADS)
    glNormal3f(0, 1, 0)
    glVertex3f(-0.5, 0.0, -0.5)
    glVertex3f(-0.5, 0.0, 0.5)
    glVertex3f(0.5, 0.0, 0.5)
    glVertex3f(0.5, 0.0, -0.5)
    glEnd()

    defineCor(corBorda)  # Desenha a borda
    glBegin(GL_LINE_STRIP)
    glNormal3f(0, 1, 0)
    glVertex3f(-0.5, 0.0, -0.5)
    glVertex3f(-0.5, 0.0, 0.5)
    glVertex3f(0.5, 0.0, 0.5)
    glVertex3f(0.5, 0.0, -0.5)
    glEnd()

# **********************************************************************
# Desenha o piso completo com ladrilhos
# **********************************************************************
def DesenhaPiso():
    random.seed(110)  # usa uma semente fixa para gerar sempre as mesma cores no piso
    glPushMatrix()
    glTranslated(CantoEsquerdo[0], CantoEsquerdo[1], CantoEsquerdo[2])
    
    for x in range(-20, 20):
        glPushMatrix()
        for z in range(-20, 20):
            DesenhaLadrilho(0, random.randint(0, 40))  # Verde para borda e uma cor aleatória
            glTranslated(0, 0, 1)
        glPopMatrix()
        glTranslated(1, 0, 0)
    
    glPopMatrix()

# **********************************************************************
# Define a iluminação da cena
# **********************************************************************
def DefineLuz():
    # Definindo cores para um objeto dourado
    LuzAmbiente = [0.4, 0.4, 0.4]
    LuzDifusa = [0.7, 0.7, 0.7]
    LuzEspecular = [0.9, 0.9, 0.9]
    PosicaoLuz0 = [0.0, 3.0, 5.0]  # Posição da luz
    Especularidade = [1.0, 1.0, 1.0]

    glEnable(GL_COLOR_MATERIAL)

    # Habilita o uso de iluminacao
    glEnable(GL_LIGHTING)

    # Ativa o uso da luz ambiente
    glLightModelfv(GL_LIGHT_MODEL_AMBIENT, LuzAmbiente)
    # Define os parametros da luz numero Zero
    glLightfv(GL_LIGHT0, GL_AMBIENT, LuzAmbiente)
    glLightfv(GL_LIGHT0, GL_DIFFUSE, LuzDifusa)
    glLightfv(GL_LIGHT0, GL_SPECULAR, LuzEspecular)
    glLightfv(GL_LIGHT0, GL_POSITION, PosicaoLuz0)
    glEnable(GL_LIGHT0)

    # Ativa o "Color Tracking"
    glEnable(GL_COLOR_MATERIAL)

    # Define a reflectancia do material
    glMaterialfv(GL_FRONT, GL_SPECULAR, Especularidade)

    # Define a concentracao do brilho.
    # Quanto maior o valor do Segundo parametro, mais
    # concentrado sera o brilho. (Valores validos: de 0 a 128)
    glMateriali(GL_FRONT, GL_SHININESS, 51)

# **********************************************************************
# Perspectiva personalizada para substituição do gluPerspective
# **********************************************************************
def MygluPerspective(fieldOfView, aspect, zNear, zFar):
    # https://stackoverflow.com/questions/2417697/gluperspective-was-removed-in-opengl-3-1-any-replacements/2417756#2417756
    # The following code is a fancy bit of math that is equivilant to calling:
    # gluPerspective( fieldOfView/2.0f, width/height , 0.1f, 255.0f )
    # We do it this way simply to avoid requiring glu.h
    # GLfloat zNear = 0.1f;
    # GLfloat zFar = 255.0f;
    # GLfloat aspect = float(width)/float(height);

    fH = math.tan(math.radians(fieldOfView / 2.0)) * zNear
    fW = fH * aspect
    glFrustum(-fW, fW, -fH, fH, zNear, zFar)

# **********************************************************************
# Função de projeção e câmera
# **********************************************************************
def PosicUser():
    # Define os parametros de projecao Perspectiva
    glMatrixMode(GL_PROJECTION)
    glLoadIdentity()

    # Define o volume de visualizacao sempre a partir da posicao do observador
    if ModoDeProjecao == 0:
        glOrtho(-10, 10, -10, 10, 0, 7)  # Projeção paralela ortográfica
    else:
        MygluPerspective(90, AspectRatio, 0.01, 50)  # Projeção perspectiva

    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()
    gluLookAt(0, 2, 3,  # Posicao do Observador
               0, 0, 0, # Posicao do Alvo 
                 0.0, 1.0, 0.0)

# **********************************************************************
# Função de redimensionamento da janela
# **********************************************************************
def reshape(w, h):
    global AspectRatio
    if h == 0:
        h = 1
    AspectRatio = float(w) / float(h)
    glViewport(0, 0, w, h)
    PosicUser()

# **********************************************************************
# Função de exibição da cena
# **********************************************************************
def display():
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
    glMatrixMode(GL_MODELVIEW)
    glLoadIdentity()

    DefineLuz()
    PosicUser()

    DesenhaPiso()

    glRotatef(angulo, 0, 1, 0)
    DesenhaObjeto3D()

    glutSwapBuffers()

# **********************************************************************
# Esta funcao captura o clique do botao direito do mouse sobre a area de
# desenho e converte a coordenada para o sistema de referencia definido
# na glOrtho (ver funcao reshape)
# Este codigo eh baseado em http://hamala.se/forums/viewtopic.php?t=20
# **********************************************************************
def Mouse(button, state, x, y):
    global PontoClicado, FoiClicado
    if state != GLUT_DOWN:
        return
    if button != GLUT_RIGHT_BUTTON:
        return

    viewport = glGetIntegerv(GL_VIEWPORT)
    modelview = glGetDoublev(GL_MODELVIEW_MATRIX)
    projection = glGetDoublev(GL_PROJECTION_MATRIX)
    wx, wy = x, y
    wy = viewport[3] - y
    wz = glReadPixels(x, y, 1, 1, GL_DEPTH_COMPONENT, GL_FLOAT)
    ox, oy, oz = gluUnProject(wx, wy, wz, modelview, projection, viewport)
    PontoClicado = (ox, oy, oz)
    FoiClicado = True

# **********************************************************************
# Função de teclado
# **********************************************************************
def keyboard(key, x, y):
    global ModoDeProjecao, ModoDeExibicao
    print ("Tecla: ", key)
    if key == b'\x1b':  # ESC
        os._exit(0)
    elif key == b'p':
        ModoDeProjecao = 1 - ModoDeProjecao
        glutPostRedisplay()
    elif key == b'e':
        ModoDeExibicao = 1 - ModoDeExibicao
        glutPostRedisplay()
    elif key == b'x':
        CriaObjetoPorExtrusaoMultipla(Base)
    else:
        print(key)

# **********************************************************************
# Função de teclas de seta
# **********************************************************************
def arrow_keys(a_keys, x, y):
    if a_keys == GLUT_KEY_UP:
        glutFullScreen()
    elif a_keys == GLUT_KEY_DOWN:
        glutInitWindowSize(700, 500)

# **********************************************************************
# Função principal
# **********************************************************************
def main():
    print("Modelagem por Extrusão")

    glutInit(sys.argv)
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_DEPTH | GLUT_RGB)
    glutInitWindowSize(700, 700)
    glutCreateWindow(b"Modelagem por Extrusao")

    init()

    glutDisplayFunc(display)
    glutIdleFunc(animate)
    glutReshapeFunc(reshape)
    glutKeyboardFunc(keyboard)
    glutSpecialFunc(arrow_keys)
    glutMouseFunc(Mouse)

    glutMainLoop()

if __name__ == '__main__':
    main()