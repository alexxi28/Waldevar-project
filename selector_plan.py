"""
Selector de zone cu probleme pe un plan (imagine sau PDF), cu zoom si
evidenta problemelor direct din interfata.

Ce face:
    - incarca o imagine (png/jpg/etc) sau un PDF (prima pagina) ca plan
    - il afiseaza pe un Canvas cu scrollbar-uri si zoom (scroll + butoane)
    - permite selectarea unei zone prin click + drag cu mouse-ul (dreptunghi)
    - la eliberarea butonului, cere o descriere scurta a problemei
    - tine o lista cu toate problemele intr-un panou lateral, unde poti:
        * edita descrierea unei probleme
        * sterge o problema anume
        * da click pe ea ca sa te duca (scroll + highlight) la zona pe harta
    - poti exporta toate zonele intr-un fisier JSON
    - poti salva o imagine finala (PNG) cu toate adnotarile deja "arse" in ea

Cum rulezi:
    python3 selector_plan.py

Zoom:
    - Ctrl + scroll mouse = zoom in/out (centrat pe cursor)
    - scroll normal = deplasare verticala
    - Shift + scroll = deplasare orizontala
    - butoanele +/- din toolbar = zoom in/out (centrat pe mijlocul ecranului)
    - butonul "100%" = reseteaza zoom-ul
"""

import json
import math
import os
import queue
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
from PIL import Image, ImageTk, ImageDraw, ImageFont

# Planurile mari (mai ales PDF-uri randate la rezolutie mare - vezi
# PDF_MAX_BASE_PIXELS) pot depasi limita implicita de "decompression bomb" a
# Pillow, gandita pentru fisiere nesigure/necunoscute. Aici marimea e produsa
# chiar de noi, deliberat si controlat prin PDF_MAX_BASE_PIXELS - dezactivam
# deci verificarea Pillow, ca sa nu riscam o eroare la un plan legitim, mare.
Image.MAX_IMAGE_PIXELS = None

try:
    import fitz  # PyMuPDF, folosit pentru citirea fisierelor PDF
    PDF_SUPPORT = True
except ImportError:
    PDF_SUPPORT = False


# Daca vrei sa nu mai apara dialogul de alegere fisier, pune aici calea
# absoluta catre imagine sau PDF (ex: "/home/alec/plan_casa.pdf"). Altfel lasa None.
DEFAULT_IMAGE_PATH = None

VIEWPORT_WIDTH = 950
VIEWPORT_HEIGHT = 700
SIDEBAR_WIDTH = 320

# Bugetul total de pixeli (latime x inaltime) pentru rasterul de baza produs
# dintr-un PDF. PDF-ul se randeaza O SINGURA DATA, la incarcare, la cel mai
# mare DPI care se incadreaza in acest buget - toate operatiile de zoom/pan
# de dupa aceea sunt doar crop+resize pe acest raster deja in memorie (rapide
# si previzibile, indiferent de complexitatea desenului), NU re-randari
# succesive din datele vectoriale ale PDF-ului. Randarea vectoriala repetata
# (o data la fiecare pas de zoom/pan) era principala sursa de lag ramasa pe
# PDF-uri complexe/CAD cu foarte multe elemente vectoriale (linii, hasuri) -
# acolo o singura randare poate dura cateva SECUNDE, imprevizibil si
# imposibil de absorbit prin debounce/throttle.
#
# Bazat pe numarul TOTAL de pixeli (nu pe DPI fix) ca sa se adapteze automat
# atat la pagini mici cat si la coli foarte mari (A0 etc.) - memoria si
# timpul de randare raman aproximativ constante indiferent de dimensiunea
# fizica a paginii. 100 milioane de pixeli inseamna cca. 300MB in memorie
# (RGB needat) si, pe un plan complex, cateva secunde la incarcare - cost
# UNIC, platit o singura data la deschiderea fisierului (vezi ecranul de
# "Se incarca..." din ProblemAreaSelector), nu la fiecare zoom/pan.
PDF_MAX_BASE_PIXELS = 100_000_000

# Nu are sens sa randam mai clar de-atat - dincolo de acest DPI, mupdf/fitz
# incepe sa refuze randarea ("Overly large image") pe pagini mici oricum.
PDF_MAX_DPI = 1200


def load_image_from_path(path):
    """Incarca o imagine dintr-un fisier, acceptand atat imagini clasice
    (png/jpg/etc) cat si PDF (randeaza prima pagina o singura data, la
    rezolutie mare, ca un raster obisnuit - vezi PDF_MAX_BASE_PIXELS)."""
    ext = os.path.splitext(path)[1].lower()

    if ext == ".pdf":
        if not PDF_SUPPORT:
            raise RuntimeError(
                "Suport PDF indisponibil: lipseste pachetul PyMuPDF.\n\n"
                "Instaleaza-l cu:\n"
                "    pip install pymupdf --break-system-packages\n"
                "sau:\n"
                "    sudo apt install python3-fitz"
            )
        doc = fitz.open(path)
        page = doc[0]  # prima pagina din PDF

        page_w_in = page.rect.width / 72
        page_h_in = page.rect.height / 72
        page_area_in2 = page_w_in * page_h_in

        dpi = PDF_MAX_DPI
        if page_area_in2 > 0:
            dpi = min(dpi, (PDF_MAX_BASE_PIXELS / page_area_in2) ** 0.5)

        # daca fitz tot refuza (pagina neobisnuit de mare/complexa), incercam
        # progresiv mai mic in loc sa crapam aplicatia la deschiderea fisierului
        image = None
        for attempt_dpi in (dpi, dpi * 0.6, dpi * 0.35, dpi * 0.2):
            try:
                zoom = attempt_dpi / 72
                pix = page.get_pixmap(matrix=fitz.Matrix(zoom, zoom))
                image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                break
            except Exception:
                continue
        doc.close()

        if image is None:
            raise RuntimeError("Pagina PDF e prea mare/complexa pentru a fi randata.")
        return image

    return Image.open(path).convert("RGB")


class ProblemAreaSelector:

    # NU permitem zoom sub 1.0 (planul deja incape complet in viewport la
    # 1.0 - "fit to window"). Sub 1.0 nu mai ramane nimic util de aratat: cea
    # mai mare parte a canvas-ului ar fi pur si simplu goala (nimic din plan
    # acolo), ceea ce arata identic cu un bug de randare (zona gri care nu
    # mai dispare niciodata) desi tehnic e "corect" - un plan mai mic decat
    # fereastra e in continuare gol in jur.
    MIN_ZOOM = 1.0
    # Marit mult (de la 20x): cum crop+resize costa la fel indiferent de
    # nivelul de zoom (bufferul randat are mereu marimea viewport-ului),
    # zoom-ul mare nu costa nimic in plus la viteza - doar la claritate
    # (dincolo de rezolutia rasterului de baza, imaginea devine usor neclara,
    # dar ramane complet utilizabila pentru inspectie detaliata).
    MAX_ZOOM = 100.0
    ZOOM_STEP_IN = 1.25
    ZOOM_STEP_OUT = 0.8

    # Cat de mult mai mare randam bitmap-ul de fundal fata de viewport-ul
    # vizibil (2.0 = 100% in plus pe fiecare dimensiune). Acest "buffer" in
    # jurul zonei vizibile face ca o panoramare/zoom rapid sa nu iasa imediat
    # in zona gri neandata - ai ceva "rezerva" de imagine deja randata pana
    # vine urmatoarea randare de calitate.
    #
    # ATENTIE la marirea acestei valori: bitmap-ul PRODUS (nu doar cel citit
    # ca sursa) are laturile de OVERSCAN * dimensiunea viewport-ului - la
    # OVERSCAN=4.0 asta insemna un bitmap de iesire de 3800x2800 (10.6
    # milioane de pixeli) la FIECARE randare, in loc de ~1900x1400 (2.7
    # milioane) la 2.0 - de 4x mai multa munca de resize la fiecare pas de
    # zoom, masurat la 100-450ms suplimentare per randare pe planul complex
    # de test. Piramida de rezolutii (vezi _build_pyramid) rezolva deja
    # problema sursei mari de citit la zoom mic, deci OVERSCAN nu mai are
    # nevoie sa fie exagerat de mare doar pentru asta - 2.0 s-a dovedit
    # suficient (testat: 0% zona gri chiar si la un burst rapid de zoom-out).
    OVERSCAN = 2.0

    # La cel mult atatea secunde una de alta, lansam o randare noua chiar
    # daca interactiunea (drag/scroll/zoom) e inca in desfasurare - nu
    # asteptam neaparat sa se opreasca mouse-ul. Fara asta, un pan/scroll
    # continuu si lung reseteaza mereu debounce-ul si bufferul OVERSCAN nu se
    # mai reimprospateaza deloc pana la eliberarea mouse-ului, ceea ce e
    # motivul principal pentru care apare zona gri la miscari mari.
    RENDER_THROTTLE_INTERVAL = 0.05

    # La fel ca RENDER_THROTTLE_INTERVAL, dar pentru preview-ul instant de
    # zoom (_show_zoom_preview). Repictarea canvas-ului (incarcarea unui
    # bitmap nou in Tk) costa cateva zeci de ms - la un scroll rapid cu multe
    # "notch"-uri pe secunda (rotita fizica de mouse sau trackpad), a face
    # asta la FIECARE notch acumuleaza si se simte exact ca lag-ul reclamat
    # la zoom. Starea (zoom_factor/scale/view) tot se actualizeaza instant la
    # fiecare eveniment - doar repictarea propriu-zisa e plafonata.
    PREVIEW_THROTTLE_INTERVAL = 0.05

    def __init__(self, root, image_path):
        self.root = root
        self.root.title("Selector zone cu probleme - " + os.path.basename(image_path))
        self.image_path = image_path

        # Incarcarea/randarea fisierului (mai ales un PDF complex - vezi
        # PDF_MAX_BASE_PIXELS) poate dura cateva secunde. E un cost UNIC, dar
        # daca l-am face sincron aici, fereastra ar aparea "inghetata" chiar
        # de la pornire, ceea ce se simte exact ca lag-ul reclamat - chiar
        # daca dupa aceea zoom/pan ar fi perfect fluide. Il facem deci pe un
        # thread de fundal si aratam un ecran de "Se incarca..." cat timp
        # asteptam, ca utilizatorul sa stie ca aplicatia lucreaza, nu ca s-a
        # blocat. Restul initializarii (in _finish_init) porneste abia dupa
        # ce imaginea/rasterul e gata.
        self.original_image = None
        self._pyramid = None
        self._load_error = None

        # Setat aici (nu in _finish_init) ca _on_close() sa functioneze corect
        # chiar daca fereastra e inchisa CAT TIMP se mai incarca fisierul
        # (inainte ca _finish_init sa apuce sa ruleze).
        self._closing = threading.Event()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        self._show_loading_screen()

        self._load_thread = threading.Thread(target=self._load_worker, daemon=True)
        self._load_thread.start()
        self.root.after(80, self._poll_load)

    def _show_loading_screen(self):
        self._loading_frame = tk.Frame(self.root, padx=60, pady=50)
        self._loading_frame.pack(expand=True)
        tk.Label(
            self._loading_frame,
            text="Se incarca planul, va rugam asteptati...",
            font=("Arial", 12),
        ).pack(pady=(0, 14))
        self._loading_progress = ttk.Progressbar(
            self._loading_frame, mode="indeterminate", length=280
        )
        self._loading_progress.pack()
        self._loading_progress.start(12)

    def _load_worker(self):
        try:
            image = load_image_from_path(self.image_path)
            self._pyramid = self._build_pyramid(image)
            # abia acum, dupa ce piramida e gata, publicam original_image -
            # _poll_load se uita doar dupa acest atribut ca sa stie ca s-a
            # terminat incarcarea (vezi mai jos)
            self.original_image = image
        except Exception as e:
            self._load_error = e

    @staticmethod
    def _build_pyramid(image):
        """Construieste un mic "pyramid" de variante ale imaginii, la
        rezolutii progresiv injumatatite, pornind de la rasterul original
        (nivelul 0 = original_image).

        La zoom mic (aproape de "fit to window" - tot planul vizibil deodata),
        zona vizibila acopera aproape TOT rasterul de baza, care poate avea
        sute de milioane de pixeli. Fara piramida, fiecare randare la acel
        nivel de zoom ar trebui sa citeasca/reduca rasterul INTREG - masurat
        la 300-1000ms per randare pe un plan complex, ceea ce se simte exact
        ca "zona gri care nu dispare" reclamata, pentru ca randarile nu mai
        apucau sa tina pasul cu zoom-ul. Avand cateva variante mai mici deja
        pregatite, alegem mereu (vezi _pick_pyramid_level) varianta cea mai
        mica care tot ofera destula rezolutie pentru zoom-ul curent, deci
        crop+resize ramane rapid (cateva ms) la orice nivel de zoom, nu doar
        la zoom mare."""
        levels = [image]
        current = image
        while max(current.size) > VIEWPORT_WIDTH * 3:
            w, h = current.size
            current = current.resize((max(1, w // 2), max(1, h // 2)), Image.BILINEAR)
            levels.append(current)
        return levels

    def _pick_pyramid_level(self, scale):
        """Alege indexul din self._pyramid a carui rezolutie e cea mai mica
        posibila fara sa fie sub ce cere `scale` curent (ca sa nu introducem
        blur suplimentar fata de ce s-ar vedea oricum din rasterul original
        la acel nivel de zoom, dar sa evitam sa citim mai multi pixeli decat
        avem nevoie)."""
        if scale <= 0:
            return len(self._pyramid) - 1
        ideal_level = math.floor(math.log2(1.0 / scale)) if scale < 1 else 0
        return max(0, min(int(ideal_level), len(self._pyramid) - 1))

    def _poll_load(self):
        if self._load_thread.is_alive():
            self.root.after(80, self._poll_load)
            return

        self._loading_progress.stop()
        self._loading_frame.destroy()

        if self._load_error is not None or self.original_image is None:
            messagebox.showerror(
                "Eroare la incarcarea fisierului",
                str(self._load_error) if self._load_error is not None else "Fisier necunoscut.",
                parent=self.root,
            )
            self.root.destroy()
            return

        self._finish_init()

    def _finish_init(self):
        # Dimensiunea REALA a canvas-ului, actualizata dinamic la redimensionare
        # (vezi on_canvas_resize). VIEWPORT_WIDTH/HEIGHT raman doar valorile
        # initiale - daca fereastra e marita/fullscreen, self.viewport_width/
        # height se actualizeaza si toate calculele de randare (zona vizibila,
        # crop, OVERSCAN) urmeaza noua dimensiune. Fara asta, la fullscreen
        # canvas-ul (widget-ul Tk) se marea vizual, dar bitmap-ul randat
        # ramanea la dimensiunea veche, mica - restul ferestrei ramanea gri
        # PERMANENT, si bufferul (dimensionat tot pentru fereastra mica)
        # devenea insuficient si pentru interactiune, aducand inapoi si
        # problemele de lag/zona gri deja rezolvate la dimensiunea originala.
        self.viewport_width = VIEWPORT_WIDTH
        self.viewport_height = VIEWPORT_HEIGHT

        self.base_scale = self._compute_fit_scale(self.original_image.size)
        self.zoom_factor = 1.0
        self.scale = self.base_scale * self.zoom_factor
        self.tk_image = None

        # Coltul din stanga-sus al zonei vizibile, in coordonate ale
        # imaginii ORIGINALE (nu scalate). Impreuna cu self.scale, defineste
        # exact ce portiune din imagine se vede in viewport.
        self.view_x = 0.0
        self.view_y = 0.0

        # Id-ul item-ului de canvas care afiseaza bitmap-ul de fundal. Creat
        # o singura data si apoi doar repozitionat/reincarcat cu imagine noua
        # (itemconfig + coords), NU sters si recreat la fiecare cadru -
        # create_image()/delete() pe canvas Tk sunt surprinzator de scumpe
        # (cateva zeci de ms per apel s-a masurat cu profiler-ul), ceea ce
        # era principala sursa de sacadare la zoom rapid (se apela la fiecare
        # "tick" de scroll pentru preview-ul instant).
        self._bg_image_id = None

        # Pentru debounce: randarea grea (crop+resize) nu se face la fiecare
        # eveniment de mouse, ci e amanata putin, ca sa nu se blocheze
        # aplicatia la miscari/scroll rapide.
        self._pending_bg_render_id = None

        # Ultimul bitmap randat "de calitate" + zona (in coordonate imagine
        # originala) si scala la care a fost randat. Folosit pentru un
        # preview INSTANT la zoom: intindem/micsoram acest bitmap deja
        # existent (rapid, e mic) cat asteptam randarea de calitate reala.
        self._last_bitmap = None
        self._last_bitmap_crop = None
        self._last_bitmap_render_scale = None

        # Randarea grea (crop+resize) ruleaza pe UN SINGUR thread de fundal,
        # persistent pe toata durata aplicatiei (pornit mai jos), care ia
        # cereri dintr-o coada. Un singur thread persistent (in loc sa
        # pornim un thread nou la fiecare cerere) evita costul de
        # creare/distrugere de threaduri la fiecare eveniment de mouse.
        #
        # Coada tine cel mult 1 element: la o cerere noua, golim orice cerere
        # veche neinceputa inca si punem doar cea mai recenta - nu are rost
        # sa randam o stare deja depasita.
        # (self._closing e setat deja in __init__, inainte de incarcare - vezi
        # acolo de ce.)
        self._render_queue = queue.Queue(maxsize=1)
        self._render_thread = threading.Thread(target=self._render_worker_loop, daemon=True)
        self._render_thread.start()

        # Momentul (time.monotonic) la care a fost lansata ultima randare -
        # folosit pentru throttle in _request_bg_render().
        self._last_render_launch_time = None
        # Momentul (time.monotonic) la care s-a repictat ultima oara preview-ul
        # de zoom - folosit pentru throttle in zoom() / _show_zoom_preview().
        self._last_preview_paint_time = None

        # Lista de zone. Fiecare element e un dict cu:
        #   id, description, original_coords [x0,y0,x1,y1] in imaginea originala
        self.areas = []
        self._next_id = 1

        # Cache pentru conturul desenului principal detectat automat (vezi
        # _detect_drawing_bbox), folosit la exportul imaginii adnotate.
        self._drawing_bbox_computed = False
        self._cached_drawing_bbox = None

        # Stare pentru selectia curenta (drag)
        self.start_x = None
        self.start_y = None
        self.current_rect_id = None

        # id_zona -> (rect_item, text_item) deja desenate pe canvas. Ne
        # permite ca la redesenare (zoom, "mergi la zona" etc.) sa doar
        # repozitionam elementele existente (canvas.coords), in loc sa le
        # stergem si sa le recream mereu de la zero - mult mai rapid cand
        # sunt multe zone.
        self._area_items = {}

        self._build_ui()
        self._render_image()

    # ------------------------------------------------------------------
    # Construire UI

    def _compute_fit_scale(self, size):
        """Scala la care planul "incape" complet in canvas (folosita ca
        referinta pentru zoom_factor=1.0/100%). Foloseste dimensiunea REALA
        curenta a canvas-ului (self.viewport_width/height), nu constantele
        initiale - ca planul sa se rescaleze corect (proportional cu
        zoom_factor-ul curent) cand fereastra e redimensionata/maximizata,
        in loc sa ramana la dimensiunea veche, mica, intr-o fereastra mare
        (exact situatia care lasa restul canvas-ului gri permanent)."""
        w, h = size
        scale_w = self.viewport_width / w
        scale_h = self.viewport_height / h
        return min(1.0, scale_w, scale_h)

    def _build_ui(self):
        # --- Toolbar sus ---
        toolbar = tk.Frame(self.root)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="-", width=3, command=lambda: self.zoom(self.ZOOM_STEP_OUT)).pack(
            side=tk.LEFT, padx=(4, 0), pady=4
        )
        tk.Button(toolbar, text="+", width=3, command=lambda: self.zoom(self.ZOOM_STEP_IN)).pack(
            side=tk.LEFT, padx=2, pady=4
        )
        tk.Button(toolbar, text="100%", command=self.reset_zoom).pack(side=tk.LEFT, padx=(2, 10), pady=4)

        self.zoom_label = tk.Label(toolbar, text="Zoom: 100%")
        self.zoom_label.pack(side=tk.LEFT, padx=(0, 10))

        tk.Button(toolbar, text="Exporta zone (JSON)", command=self.export_json).pack(
            side=tk.LEFT, padx=4, pady=4
        )
        tk.Button(
            toolbar, text="Salveaza imagine adnotata", command=self.export_annotated_image
        ).pack(side=tk.LEFT, padx=4, pady=4)
        tk.Button(toolbar, text="Sterge tot", command=self.clear_all).pack(
            side=tk.LEFT, padx=4, pady=4
        )

        tk.Label(
            toolbar,
            text="Click stanga + tragere = navigheaza  |  Click dreapta + tragere = marcheaza zona",
            fg="gray30",
        ).pack(side=tk.LEFT, padx=10)

        # --- Zona principala: canvas (stanga) + sidebar (dreapta) ---
        main_frame = tk.Frame(self.root)
        main_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        canvas_frame = tk.Frame(main_frame)
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        h_scroll = tk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL, command=self.on_hscroll)
        v_scroll = tk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.on_vscroll)
        self.h_scroll = h_scroll
        self.v_scroll = v_scroll

        self.canvas = tk.Canvas(
            canvas_frame,
            width=VIEWPORT_WIDTH,
            height=VIEWPORT_HEIGHT,
            cursor="fleur",
            bg="gray80",
        )

        self.canvas.grid(row=0, column=0, sticky="nsew")
        v_scroll.grid(row=0, column=1, sticky="ns")
        h_scroll.grid(row=1, column=0, sticky="ew")
        canvas_frame.rowconfigure(0, weight=1)
        canvas_frame.columnconfigure(0, weight=1)

        self._build_sidebar(main_frame)

        self.status = tk.Label(self.root, text="Zone selectate: 0", anchor="w")
        self.status.pack(side=tk.BOTTOM, fill=tk.X)

        # Urmarim dimensiunea REALA a canvas-ului (se schimba la redimensionarea
        # ferestrei/fullscreen, chiar daca VIEWPORT_WIDTH/HEIGHT raman fixe -
        # canvas-ul e "sticky=nsew" cu weight=1, deci Tk il intinde automat).
        self.canvas.bind("<Configure>", self.on_canvas_resize)

        # Click stanga + tragere = navigare libera prin desen (pan), ca in AutoCAD
        self.canvas.bind("<ButtonPress-1>", self.on_pan_start)
        self.canvas.bind("<B1-Motion>", self.on_pan_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_pan_end)

        # Click dreapta + tragere = marcheaza o zona cu problema
        self.canvas.bind("<ButtonPress-3>", self.on_mark_start)
        self.canvas.bind("<B3-Motion>", self.on_mark_drag)
        self.canvas.bind("<ButtonRelease-3>", self.on_mark_end)

        # Zoom cu Ctrl + scroll (Windows/Mac)
        self.canvas.bind("<Control-MouseWheel>", self.on_ctrl_mousewheel)
        # Zoom cu Ctrl + scroll (Linux, unde scroll-ul e Button-4/5)
        self.canvas.bind("<Control-Button-4>", lambda e: self.zoom(self.ZOOM_STEP_IN, e))
        self.canvas.bind("<Control-Button-5>", lambda e: self.zoom(self.ZOOM_STEP_OUT, e))

        # Scroll normal (fara Ctrl) = deplasare verticala/orizontala
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)
        self.canvas.bind("<Shift-MouseWheel>", self.on_shift_mousewheel)
        self.canvas.bind("<Button-4>", lambda e: self.pan(0, -1))
        self.canvas.bind("<Button-5>", lambda e: self.pan(0, 1))

        # Scurtaturi de tastatura pentru zoom
        self.root.bind("<Control-plus>", lambda e: self.zoom(self.ZOOM_STEP_IN))
        self.root.bind("<Control-equal>", lambda e: self.zoom(self.ZOOM_STEP_IN))
        self.root.bind("<Control-minus>", lambda e: self.zoom(self.ZOOM_STEP_OUT))
        self.root.bind("<Control-0>", lambda e: self.reset_zoom())

    def _on_close(self):
        # opreste thread-ul de fundal INAINTE sa distrugem fereastra, ca sa
        # nu mai incerce sa predea un rezultat catre un root deja disparut.
        # Legat deja de WM_DELETE_WINDOW in __init__, inainte de incarcare,
        # ca sa functioneze si daca fereastra e inchisa in timpul ecranului
        # de "Se incarca...".
        self._closing.set()
        self.root.destroy()

    def _build_sidebar(self, parent):
        sidebar = tk.Frame(parent, width=SIDEBAR_WIDTH)
        sidebar.pack(side=tk.RIGHT, fill=tk.Y)
        sidebar.pack_propagate(False)

        tk.Label(sidebar, text="Probleme identificate", font=("Arial", 11, "bold")).pack(
            side=tk.TOP, anchor="w", padx=6, pady=(6, 2)
        )

        list_frame = tk.Frame(sidebar)
        list_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=6)

        list_scroll = tk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.problem_listbox = tk.Listbox(
            list_frame, yscrollcommand=list_scroll.set, activestyle="none", exportselection=False
        )
        list_scroll.config(command=self.problem_listbox.yview)
        self.problem_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        list_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        self.problem_listbox.bind("<<ListboxSelect>>", self.on_problem_selected)
        self.problem_listbox.bind("<Double-Button-1>", lambda e: self.go_to_selected())

        btns = tk.Frame(sidebar)
        btns.pack(side=tk.TOP, fill=tk.X, padx=6, pady=6)

        tk.Button(btns, text="Mergi la zona", command=self.go_to_selected).pack(fill=tk.X, pady=2)
        tk.Button(btns, text="Editeaza descrierea", command=self.edit_selected).pack(fill=tk.X, pady=2)
        tk.Button(btns, text="Sterge problema", command=self.delete_selected).pack(fill=tk.X, pady=2)

        # Panou de detalii pentru problema selectata
        tk.Label(sidebar, text="Detalii:", font=("Arial", 9, "bold")).pack(
            side=tk.TOP, anchor="w", padx=6, pady=(8, 0)
        )
        self.detail_text = tk.Text(sidebar, height=8, wrap="word", state="disabled")
        self.detail_text.pack(side=tk.TOP, fill=tk.X, padx=6, pady=(0, 6))

    # ------------------------------------------------------------------
    # Randare imagine + zoom

    def _visible_size_in_original(self):
        """Latimea/inaltimea (in pixeli din imaginea ORIGINALA) pe care o
        acopera viewport-ul la zoom-ul curent. Foloseste dimensiunea REALA,
        curenta a canvas-ului (self.viewport_width/height), nu constantele
        initiale - altfel la fullscreen/redimensionare bitmap-ul randat ar
        ramane la dimensiunea veche, mica, iar restul canvas-ului ar ramane
        gri permanent."""
        return self.viewport_width / self.scale, self.viewport_height / self.scale

    def on_canvas_resize(self, event):
        """Cand se schimba dimensiunea REALA a canvas-ului (redimensionarea
        ferestrei, maximizare, fullscreen) - vezi comentariul de la
        self.viewport_width din _finish_init pentru motivul pentru care asta
        conteaza. Evenimentul <Configure> poate veni foarte des cat timp
        utilizatorul trage de marginea ferestrei (sau chiar la simpla mutare
        a ferestrei, fara schimbare de dimensiune - de-aia verificam explicit
        daca s-a schimbat ceva), deci randarea grea trece prin acelasi
        mecanism de debounce/throttle ca zoom-ul si panoramarea."""
        new_w, new_h = event.width, event.height
        if new_w == self.viewport_width and new_h == self.viewport_height:
            return

        # pastram centrul actual (in coordonate imagine originala) fix pe
        # ecran dupa recalcularea scalei, ca redimensionarea sa nu "sara"
        old_visible_w, old_visible_h = self._visible_size_in_original()
        center_x = self.view_x + old_visible_w / 2
        center_y = self.view_y + old_visible_h / 2

        self.viewport_width = new_w
        self.viewport_height = new_h

        # planul se rescaleaza proportional cu noua dimensiune a canvas-ului,
        # pastrand zoom_factor-ul curent - la 100% (fit to window), asta
        # inseamna ca planul creste/scade odata cu fereastra, ca intr-un
        # viewer de imagini normal, in loc sa ramana la dimensiunea veche cu
        # spatiu gol (gri) in jur intr-o fereastra mult mai mare.
        self.base_scale = self._compute_fit_scale(self.original_image.size)
        self.scale = self.base_scale * self.zoom_factor

        new_visible_w, new_visible_h = self._visible_size_in_original()
        self.view_x = center_x - new_visible_w / 2
        self.view_y = center_y - new_visible_h / 2

        self._clamp_view()
        self._update_ui_state()
        self._request_bg_render(delay=80)

    def _clamp_view(self):
        w, h = self.original_image.size
        visible_w, visible_h = self._visible_size_in_original()

        max_x = max(0.0, w - visible_w)
        max_y = max(0.0, h - visible_h)
        self.view_x = min(max(0.0, self.view_x), max_x)
        self.view_y = min(max(0.0, self.view_y), max_y)

    def _render_image(self):
        """Randare completa, IMEDIATA (folosita la actiuni discrete: incarcare
        initiala, reset zoom, click pe buton 'Mergi la zona' etc). E singura
        randare care ramane sincrona (blocheaza pentru o clipa), pentru ca
        se intampla o singura data, nu in mijlocul unei interactiuni continue.
        Pentru evenimente rapide/continue (drag, scroll), NU se apeleaza
        direct aceasta metoda - vezi _request_bg_render() mai jos."""
        if self._pending_bg_render_id is not None:
            self.root.after_cancel(self._pending_bg_render_id)
            self._pending_bg_render_id = None
        self._clamp_view()
        self._update_ui_state()
        crop_params = self._capture_crop_params()
        resized = self._produce_bitmap(crop_params)
        self._apply_bitmap_result(resized, crop_params)

    def _update_ui_state(self):
        """Partea ieftina: pozitiile dreptunghiurilor, eticheta de zoom,
        scrollbar-urile. Nu implica nicio decodare/randare de imagine, deci
        se poate apela oricat de des fara sa incetineasca aplicatia."""
        self.zoom_label.config(text=f"Zoom: {int(round(self.zoom_factor * 100))}%")
        self._update_scrollbars()
        self._redraw_areas()

    def _capture_crop_params(self, interactive=False):
        """Calculeaza zona (in coordonate imagine originala) care trebuie
        randata, incluzand marginea OVERSCAN, plus scala curenta - tot ce
        e nevoie pentru a produce bitmap-ul, capturat ca o "poza" a starii
        curente (sigur de trecut si intr-un thread de fundal).

        `interactive=True` marcheaza o randare ceruta CAT TIMP utilizatorul
        inca trage de mouse/da scroll (nu s-a oprit inca) - vezi
        _produce_bitmap() pentru ce inseamna asta in practica."""
        w, h = self.original_image.size
        visible_w, visible_h = self._visible_size_in_original()

        margin_w = visible_w * (self.OVERSCAN - 1) / 2
        margin_h = visible_h * (self.OVERSCAN - 1) / 2

        crop_x0 = max(0.0, self.view_x - margin_w)
        crop_y0 = max(0.0, self.view_y - margin_h)
        crop_x1 = min(w, self.view_x + visible_w + margin_w)
        crop_y1 = min(h, self.view_y + visible_h + margin_h)

        return {
            "crop": (crop_x0, crop_y0, crop_x1, crop_y1),
            "scale": self.scale,
            "interactive": interactive,
        }

    def _produce_bitmap(self, crop_params):
        """Partea scumpa, dar PURA (nu atinge self.view_x/self.scale/canvas):
        produce bitmap-ul PIL pentru crop_params dati. Poate fi apelata direct
        (randare sincrona) sau dintr-un thread de fundal (randare asincrona),
        pentru ca nu modifica nicio stare comuna in timp ce ruleaza.

        Cand crop_params["interactive"] e True (utilizatorul inca trage de
        mouse/da scroll), folosim un resampling mult mai rapid (BILINEAR in
        loc de LANCZOS) - vizibil putin mai neclar, dar de multe ori mai
        rapid pe crop-uri mari, ceea ce e principalul motiv de lag la
        panoramare/zoom. Cand interactiunea se opreste, urmeaza automat o
        randare finala cu interactive=False, care aduce claritatea maxima
        (LANCZOS). Se aplica identic pentru imagini si PDF-uri - PDF-ul e deja
        randat o singura data la incarcare (vezi load_image_from_path), deci
        aici e mereu vorba de un simplu crop+resize, niciodata o re-randare
        din date vectoriale.

        Crop-ul nu se face mereu din self.original_image (nivelul 0, plin) -
        vezi _pick_pyramid_level: la zoom mic, unde zona vizibila acopera
        aproape tot rasterul, cropul de pe nivelul 0 ar avea sute de milioane
        de pixeli si resize-ul ar dura sute de ms la fiecare randare
        (masurat: pana la ~1s pe un plan complex) - exact sursa "zonei gri
        care nu dispare" la zoom mic/zoom-out rapid. Folosind un nivel deja
        micsorat din piramida cand e suficient, crop+resize ramane rapid
        (cateva ms) la ORICE nivel de zoom."""
        crop_x0, crop_y0, crop_x1, crop_y1 = crop_params["crop"]
        scale = crop_params["scale"]
        interactive = crop_params.get("interactive", False)

        level_idx = self._pick_pyramid_level(scale)
        level_image = self._pyramid[level_idx]
        level_factor = 2 ** level_idx

        crop = level_image.crop((
            int(crop_x0 / level_factor),
            int(crop_y0 / level_factor),
            int(round(crop_x1 / level_factor)),
            int(round(crop_y1 / level_factor)),
        ))
        target_w = max(1, round((crop_x1 - crop_x0) * scale))
        target_h = max(1, round((crop_y1 - crop_y0) * scale))
        resample = Image.BILINEAR if interactive else Image.LANCZOS
        return crop.resize((target_w, target_h), resample)

    def _apply_bitmap_result(self, resized, crop_params):
        """Aplica un bitmap deja produs: il retine ca 'ultimul bitmap bun'
        (pentru preview-ul de zoom) si il afiseaza pe canvas."""
        crop_x0, crop_y0, crop_x1, crop_y1 = crop_params["crop"]
        self._last_bitmap = resized
        self._last_bitmap_crop = (crop_x0, crop_y0, crop_x1, crop_y1)
        self._last_bitmap_render_scale = crop_params["scale"]
        self._show_bitmap(resized, crop_x0, crop_y0)

    def _show_bitmap(self, pil_image, crop_x0, crop_y0):
        """Afiseaza pe canvas un bitmap deja pregatit (PIL Image), pozitionat
        astfel incat coltul (crop_x0, crop_y0) - in coordonate ale imaginii
        originale - sa cada exact unde trebuie fata de view-ul curent.

        Reutilizeaza acelasi item de canvas (itemconfig + coords) in loc sa
        stearga si sa recreeze imaginea de fiecare data - vezi comentariul de
        la self._bg_image_id in __init__ pentru motiv."""
        self.tk_image = ImageTk.PhotoImage(pil_image)

        offset_x = (crop_x0 - self.view_x) * self.scale
        offset_y = (crop_y0 - self.view_y) * self.scale

        if self._bg_image_id is None:
            self._bg_image_id = self.canvas.create_image(
                offset_x, offset_y, anchor=tk.NW, image=self.tk_image, tags="bg"
            )
            self.canvas.tag_lower("bg")
        else:
            self.canvas.itemconfig(self._bg_image_id, image=self.tk_image)
            self.canvas.coords(self._bg_image_id, offset_x, offset_y)

    def _request_bg_render(self, delay=80):
        """Cerere de randare in timpul unei interactiuni continue
        (drag/scroll/zoom). Doua lucruri se intampla:

        1. Se lanseaza IMEDIAT o randare RAPIDA/interactiva (calitate redusa,
           vezi _produce_bitmap), dar doar daca a trecut deja
           RENDER_THROTTLE_INTERVAL de la ultima randare lansata - asta tine
           bufferul OVERSCAN reimprospatat CAT TIMP interactiunea continua,
           nu doar la final. Fara asta, un drag/scroll continuu si lung ar
           reseta mereu orice debounce si bufferul nu s-ar mai reimprospata
           deloc pana la eliberarea mouse-ului - motivul principal pentru
           care aparea zona gri la miscari mari.
        2. Se (re)programeaza o randare FINALA de calitate maxima peste
           `delay` ms - daca intre timp mai vine o cerere, cea veche se
           anuleaza si se reprogrameaza. Cand utilizatorul chiar se opreste,
           aceasta e cea care aduce imaginea la claritate maxima."""
        if self._pending_bg_render_id is not None:
            self.root.after_cancel(self._pending_bg_render_id)
        self._pending_bg_render_id = self.root.after(delay, self._do_scheduled_bg_render)

        now = time.monotonic()
        if (
            self._last_render_launch_time is None
            or (now - self._last_render_launch_time) >= self.RENDER_THROTTLE_INTERVAL
        ):
            self._launch_bg_render(interactive=True)

    def _do_scheduled_bg_render(self):
        """Randarea "de coada": porneste doar daca timp de `delay` ms nu a
        mai venit nicio alta cerere - adica interactiunea chiar s-a oprit.
        Intotdeauna la calitate maxima (interactive=False)."""
        self._pending_bg_render_id = None
        self._clamp_view()
        self._update_ui_state()
        self._launch_bg_render(interactive=False)

    def _launch_bg_render(self, interactive=False):
        """Trimite o cerere de randare in coada thread-ului de fundal
        persistent, ca sa nu blocheze deloc interfata (asta era motivul
        pentru care aplicatia "ingheta" vizibil la zoom mare + panoramare
        mare: randarea sincrona putea dura sute de milisecunde, timp in care
        fereastra nu raspundea deloc).

        Coada tine cel mult 1 cerere: daca vine una noua inainte ca thread-ul
        sa apuce s-o preia pe cea veche, o inlocuim - nu are rost sa randam
        o stare deja depasita."""
        self._last_render_launch_time = time.monotonic()
        crop_params = self._capture_crop_params(interactive=interactive)

        try:
            while True:
                self._render_queue.get_nowait()
        except queue.Empty:
            pass
        self._render_queue.put(crop_params)

    def _render_worker_loop(self):
        """Ruleaza PE THREAD-UL DE FUNDAL, o singura data pentru toata durata
        aplicatiei. Asteapta cereri in coada si le proceseaza una cate una -
        nu atinge widget-uri Tkinter direct (nu e permis din alt thread),
        doar calculeaza bitmap-ul, apoi preda rezultatul inapoi firului
        principal prin root.after()."""
        while True:
            crop_params = self._render_queue.get()
            if self._closing.is_set():
                return
            try:
                resized = self._produce_bitmap(crop_params)
            except Exception:
                resized = None
            if self._closing.is_set():
                return
            try:
                self.root.after(0, self._on_bg_render_done, resized, crop_params)
            except RuntimeError:
                return  # fereastra a fost inchisa chiar in acest interval

    def _on_bg_render_done(self, resized, crop_params):
        """Ruleaza pe firul principal (via root.after), deci poate atinge
        canvas-ul in siguranta."""
        if resized is not None:
            self._apply_bitmap_result(resized, crop_params)

    def _update_scrollbars(self):
        w, h = self.original_image.size
        visible_w, visible_h = self._visible_size_in_original()

        first_x = self.view_x / w if w > 0 else 0
        last_x = min(1.0, (self.view_x + visible_w) / w) if w > 0 else 1
        first_y = self.view_y / h if h > 0 else 0
        last_y = min(1.0, (self.view_y + visible_h) / h) if h > 0 else 1

        self.h_scroll.set(first_x, last_x)
        self.v_scroll.set(first_y, last_y)

    # coordonate: din pixeli-widget (ce vede utilizatorul) in pixeli ai
    # imaginii originale, tinand cont de pan (view_x/view_y) si zoom (scale)
    def widget_to_original(self, wx, wy):
        return self.view_x + wx / self.scale, self.view_y + wy / self.scale

    def original_to_widget(self, ox, oy):
        return (ox - self.view_x) * self.scale, (oy - self.view_y) * self.scale

    def zoom(self, factor, event=None):
        new_zoom = self.zoom_factor * factor
        new_zoom = max(self.MIN_ZOOM, min(self.MAX_ZOOM, new_zoom))
        if abs(new_zoom - self.zoom_factor) < 1e-9:
            return

        if event is not None:
            widget_x, widget_y = event.x, event.y
        else:
            widget_x = self.viewport_width / 2
            widget_y = self.viewport_height / 2

        # punctul din imaginea originala aflat sub cursor, ca sa ramana
        # fix pe ecran dupa schimbarea zoom-ului (zoom centrat pe cursor)
        orig_x, orig_y = self.widget_to_original(widget_x, widget_y)

        self.zoom_factor = new_zoom
        self.scale = self.base_scale * self.zoom_factor

        self.view_x = orig_x - widget_x / self.scale
        self.view_y = orig_y - widget_y / self.scale
        self._clamp_view()

        # feedback ieftin si instantaneu (pozitii, procent zoom, scrollbar);
        # randarea grea (crop/resize) e amanata, ca sa nu se blocheze
        # aplicatia daca dai scroll rapid de mai multe ori la rand
        self._update_ui_state()

        # repictarea propriu-zisa a preview-ului e plafonata (vezi
        # PREVIEW_THROTTLE_INTERVAL) - la un scroll foarte rapid, unele
        # "notch"-uri intermediare nu mai declanseaza o repictare separata,
        # dar starea de zoom ramane mereu corecta si randarea finala de
        # calitate tot vine (vezi _request_bg_render mai jos)
        now = time.monotonic()
        if (
            self._last_preview_paint_time is None
            or (now - self._last_preview_paint_time) >= self.PREVIEW_THROTTLE_INTERVAL
        ):
            self._last_preview_paint_time = now
            self._show_zoom_preview()

        self._request_bg_render(delay=60)

    def _show_zoom_preview(self):
        """Cat timp asteptam randarea de calitate (thread de fundal), intindem/
        micsoram instant bitmap-ul deja randat, ca fundalul sa urmareasca
        zoom-ul in timp real (aproximativ, usor neclar) in loc sa ramana
        "inghetat" la scara veche pana vine randarea reala - asta era
        senzatia de lag/salt la zoom.

        Important: luam doar portiunea din bitmap-ul vechi care corespunde
        zonei ACUM vizibile (nu tot tile-ul randat anterior), asa ca durata
        acestui preview ramane mica si constanta (proportionala cu
        viewport-ul), indiferent cat de mult s-a schimbat zoom-ul intre
        timp - inainte, la zoom-uri rapide repetate, tile-ul intreg trebuia
        umflat la un raport din ce in ce mai mare si depasea rapid limita
        de siguranta, motiv pentru care preview-ul parea ca "ingheata"."""
        if (
            self._last_bitmap is None
            or self._last_bitmap_render_scale is None
            or self._last_bitmap_crop is None
        ):
            return

        old_crop_x0, old_crop_y0, _, _ = self._last_bitmap_crop
        old_scale = self._last_bitmap_render_scale
        ratio = self.scale / old_scale

        visible_w, visible_h = self._visible_size_in_original()
        bw, bh = self._last_bitmap.size

        # zona nou-vizibila (in coordonate originale), exprimata in pixelii
        # bitmap-ului vechi deja randat
        px0 = (self.view_x - old_crop_x0) * old_scale
        py0 = (self.view_y - old_crop_y0) * old_scale
        px1 = (self.view_x + visible_w - old_crop_x0) * old_scale
        py1 = (self.view_y + visible_h - old_crop_y0) * old_scale

        # taiem la marginile bitmap-ului existent - daca zona ceruta iese
        # din ce aveam deja randat, nu putem inventa pixeli noi de acolo;
        # ramane vizibil gri in acea portiune pana vine randarea reala
        cpx0 = max(0.0, min(px0, bw))
        cpy0 = max(0.0, min(py0, bh))
        cpx1 = max(0.0, min(px1, bw))
        cpy1 = max(0.0, min(py1, bh))

        if cpx1 - cpx0 < 1 or cpy1 - cpy0 < 1:
            return  # nu mai ramane nimic util de aratat din bitmap-ul vechi

        sub = self._last_bitmap.crop((int(cpx0), int(cpy0), int(round(cpx1)), int(round(cpy1))))

        target_w = max(1, round((cpx1 - cpx0) * ratio))
        target_h = max(1, round((cpy1 - cpy0) * ratio))
        if target_w > 4000 or target_h > 4000:
            return  # siguranta suplimentara pentru cazuri extreme
        preview = sub.resize((target_w, target_h), Image.BILINEAR)

        crop_x0 = old_crop_x0 + cpx0 / old_scale
        crop_y0 = old_crop_y0 + cpy0 / old_scale
        self._show_bitmap(preview, crop_x0, crop_y0)

    def reset_zoom(self):
        self.zoom_factor = 1.0
        self.scale = self.base_scale * self.zoom_factor
        self.view_x = 0.0
        self.view_y = 0.0
        self._render_image()

    def pan(self, dx_units, dy_units):
        """Deplaseaza vizualizarea. Unitatea e o fractiune din viewport-ul
        vizibil curent (ca sa se simta la fel la orice nivel de zoom)."""
        visible_w, visible_h = self._visible_size_in_original()
        self.view_x += dx_units * visible_w * 0.1
        self.view_y += dy_units * visible_h * 0.1
        self._clamp_view()
        self._update_ui_state()
        self._request_bg_render(delay=80)

    def on_hscroll(self, *args):
        w, _ = self.original_image.size
        visible_w, _ = self._visible_size_in_original()
        if args[0] == "moveto":
            frac = float(args[1])
            self.view_x = frac * w
        elif args[0] == "scroll":
            amount = int(args[1])
            unit = args[2] if len(args) > 2 else "units"
            step = visible_w * (0.9 if unit == "pages" else 0.1)
            self.view_x += amount * step
        self._clamp_view()
        self._update_ui_state()
        self._request_bg_render(delay=80)

    def on_vscroll(self, *args):
        _, h = self.original_image.size
        _, visible_h = self._visible_size_in_original()
        if args[0] == "moveto":
            frac = float(args[1])
            self.view_y = frac * h
        elif args[0] == "scroll":
            amount = int(args[1])
            unit = args[2] if len(args) > 2 else "units"
            step = visible_h * (0.9 if unit == "pages" else 0.1)
            self.view_y += amount * step
        self._clamp_view()
        self._update_ui_state()
        self._request_bg_render(delay=80)

    def on_ctrl_mousewheel(self, event):
        if event.delta > 0:
            self.zoom(self.ZOOM_STEP_IN, event)
        else:
            self.zoom(self.ZOOM_STEP_OUT, event)

    def on_mousewheel(self, event):
        direction = -1 if event.delta > 0 else 1
        self.pan(0, direction)

    def on_shift_mousewheel(self, event):
        direction = -1 if event.delta > 0 else 1
        self.pan(direction, 0)

    # ------------------------------------------------------------------
    # Evenimente mouse (selectie zona)

    def on_pan_start(self, event):
        self._pan_last_x = event.x
        self._pan_last_y = event.y
        self.canvas.config(cursor="fleur")

    def on_pan_drag(self, event):
        dx = event.x - self._pan_last_x
        dy = event.y - self._pan_last_y
        self._pan_last_x = event.x
        self._pan_last_y = event.y

        self.view_x -= dx / self.scale
        self.view_y -= dy / self.scale
        self._clamp_view()

        # feedback INSTANTANEU si ieftin: mutam bitmap-ul deja randat SI
        # dreptunghiurile/etichetele zonelor deja desenate (canvas.move),
        # in loc sa le stergem si sa le recream de la zero la fiecare
        # eveniment de mouse. Recrearea (delete + create_rectangle/create_text
        # pt fiecare zona, de zeci de ori pe secunda in timpul unui drag) era
        # principalul motiv de lag - .move() e aproape gratuit in schimb.
        self.canvas.move("bg", dx, dy)
        self.canvas.move("area", dx, dy)
        self._update_scrollbars()

        # randarea de calitate (crop/resize) e amanata; daca miscarea
        # continua, cererea veche e anulata si reprogramata
        self._request_bg_render(delay=80)

    def on_pan_end(self, event):
        # la eliberarea mouse-ului, pornim imediat randarea finala de
        # calitate, dar PE THREAD DE FUNDAL (nu mai blocheaza interfata,
        # nici chiar daca a fost un drag mare la zoom mare)
        if self._pending_bg_render_id is not None:
            self.root.after_cancel(self._pending_bg_render_id)
            self._pending_bg_render_id = None
        self._clamp_view()
        self._update_ui_state()
        self._launch_bg_render()

    def on_mark_start(self, event):
        self.start_x = event.x
        self.start_y = event.y
        self.current_rect_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, self.start_x, self.start_y,
            outline="lime", width=2, tags="selection_in_progress"
        )

    def on_mark_drag(self, event):
        if self.current_rect_id is None:
            return
        self.canvas.coords(self.current_rect_id, self.start_x, self.start_y, event.x, event.y)

    def on_mark_end(self, event):
        if self.current_rect_id is None:
            return

        end_x, end_y = event.x, event.y

        x0, x1 = sorted((self.start_x, end_x))
        y0, y1 = sorted((self.start_y, end_y))

        if abs(x1 - x0) < 5 or abs(y1 - y0) < 5:
            self.canvas.delete(self.current_rect_id)
            self.current_rect_id = None
            return

        description = simpledialog.askstring(
            "Descriere problema",
            "Descrie problema din zona selectata:",
            parent=self.root,
        )

        self.canvas.delete(self.current_rect_id)
        self.current_rect_id = None

        if not description:
            return

        orig_x0, orig_y0 = self.widget_to_original(x0, y0)
        orig_x1, orig_y1 = self.widget_to_original(x1, y1)

        orig_coords = [round(orig_x0), round(orig_y0), round(orig_x1), round(orig_y1)]

        area = {
            "id": self._next_id,
            "description": description,
            "original_coords": orig_coords,
        }
        self._next_id += 1
        self.areas.append(area)

        self._redraw_areas()
        self._refresh_problem_list(select_id=area["id"])

    # ------------------------------------------------------------------
    # Desenare zone pe canvas (in functie de zoom-ul curent)

    def _redraw_areas(self):
        current_ids = {area["id"] for area in self.areas}

        # curata elementele zonelor sterse intre timp
        for aid in list(self._area_items.keys()):
            if aid not in current_ids:
                rect_id, text_id = self._area_items.pop(aid)
                self.canvas.delete(rect_id, text_id)

        for area in self.areas:
            ox0, oy0, ox1, oy1 = area["original_coords"]
            x0, y0 = self.original_to_widget(ox0, oy0)
            x1, y1 = self.original_to_widget(ox1, oy1)

            existing = self._area_items.get(area["id"])
            if existing is not None:
                # zona exista deja pe canvas: doar ii mutam coordonatele,
                # fara sa stergem/recream elementele (mult mai rapid)
                rect_id, text_id = existing
                self.canvas.coords(rect_id, x0, y0, x1, y1)
                self.canvas.coords(text_id, x0 + 4, y0 - 10)
            else:
                rect_id = self.canvas.create_rectangle(
                    x0, y0, x1, y1, outline="red", width=2,
                    tags=("area", f"area_{area['id']}")
                )
                text_id = self.canvas.create_text(
                    x0 + 4, y0 - 10, anchor=tk.W,
                    text=f"#{area['id']}", fill="red",
                    font=("Arial", 10, "bold"),
                    tags=("area", f"area_{area['id']}")
                )
                self._area_items[area["id"]] = (rect_id, text_id)

        self._update_status()

    def _update_status(self):
        self.status.config(text=f"Zone selectate: {len(self.areas)}")

    # ------------------------------------------------------------------
    # Panou lateral (lista de probleme)

    def _refresh_problem_list(self, select_id=None):
        self.problem_listbox.delete(0, tk.END)
        for area in self.areas:
            snippet = area["description"].splitlines()[0]
            if len(snippet) > 40:
                snippet = snippet[:37] + "..."
            self.problem_listbox.insert(tk.END, f"#{area['id']}  {snippet}")

        if select_id is not None:
            for idx, area in enumerate(self.areas):
                if area["id"] == select_id:
                    self.problem_listbox.selection_clear(0, tk.END)
                    self.problem_listbox.selection_set(idx)
                    self.problem_listbox.see(idx)
                    self._show_details(area)
                    break
        else:
            self._show_details(None)

    def _get_selected_area(self):
        sel = self.problem_listbox.curselection()
        if not sel:
            return None
        return self.areas[sel[0]]

    def _show_details(self, area):
        self.detail_text.config(state="normal")
        self.detail_text.delete("1.0", tk.END)
        if area is not None:
            self.detail_text.insert(
                tk.END,
                f"Problema #{area['id']}\n\n{area['description']}\n\n"
                f"Coordonate (imagine originala): {area['original_coords']}"
            )
        self.detail_text.config(state="disabled")

    def on_problem_selected(self, event=None):
        area = self._get_selected_area()
        self._show_details(area)

    def go_to_selected(self):
        area = self._get_selected_area()
        if area is None:
            messagebox.showinfo("Info", "Selecteaza mai intai o problema din lista.")
            return

        ox0, oy0, ox1, oy1 = area["original_coords"]
        center_x = (ox0 + ox1) / 2
        center_y = (oy0 + oy1) / 2
        visible_w, visible_h = self._visible_size_in_original()

        self.view_x = center_x - visible_w / 2
        self.view_y = center_y - visible_h / 2
        self._render_image()

        self._flash_highlight(area["id"])

    def _flash_highlight(self, area_id, times=6):
        tag = f"area_{area_id}"
        items = self.canvas.find_withtag(tag)
        rects = [i for i in items if self.canvas.type(i) == "rectangle"]
        if not rects:
            return

        def toggle(count):
            color = "yellow" if count % 2 == 0 else "red"
            for r in rects:
                self.canvas.itemconfig(r, outline=color, width=3 if color == "yellow" else 2)
            if count < times:
                self.root.after(200, toggle, count + 1)

        toggle(0)

    def edit_selected(self):
        area = self._get_selected_area()
        if area is None:
            messagebox.showinfo("Info", "Selecteaza mai intai o problema din lista.")
            return

        new_description = simpledialog.askstring(
            "Editeaza descriere",
            "Descrierea problemei:",
            initialvalue=area["description"],
            parent=self.root,
        )
        if new_description:
            area["description"] = new_description
            self._refresh_problem_list(select_id=area["id"])

    def delete_selected(self):
        area = self._get_selected_area()
        if area is None:
            messagebox.showinfo("Info", "Selecteaza mai intai o problema din lista.")
            return

        if messagebox.askyesno("Confirmare", f"Stergi problema #{area['id']}?"):
            self.areas.remove(area)
            self._redraw_areas()
            self._refresh_problem_list()

    def clear_all(self):
        if not self.areas:
            return
        if messagebox.askyesno("Confirmare", "Stergi toate zonele selectate?"):
            self.areas.clear()
            self._redraw_areas()
            self._refresh_problem_list()

    # ------------------------------------------------------------------
    # Export

    def export_json(self):
        if not self.areas:
            messagebox.showinfo("Info", "Nu ai nicio zona selectata inca.")
            return

        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            initialfile="zone_probleme.json",
        )
        if not path:
            return

        export_data = [
            {
                "id": a["id"],
                "descriere": a["description"],
                "coordonate_imagine_originala": a["original_coords"],
            }
            for a in self.areas
        ]

        with open(path, "w", encoding="utf-8") as f:
            json.dump(export_data, f, ensure_ascii=False, indent=2)

        messagebox.showinfo("Succes", f"Zonele au fost exportate in:\n{path}")

    def export_annotated_image(self):
        if not self.areas:
            messagebox.showinfo("Info", "Nu ai nicio zona selectata inca.")
            return

        path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG", "*.png")],
            initialfile="plan_adnotat.png",
        )
        if not path:
            return

        annotated = self.original_image.copy()
        draw = ImageDraw.Draw(annotated)

        try:
            font = ImageFont.truetype("DejaVuSans-Bold.ttf", 20)
        except Exception:
            font = ImageFont.load_default()

        for area in self.areas:
            x0, y0, x1, y1 = area["original_coords"]
            draw.rectangle([x0, y0, x1, y1], outline="red", width=3)
            draw.text((x0 + 4, max(0, y0 - 22)), f"#{area['id']}", fill="red", font=font)

        cropped = self._crop_to_areas(annotated)
        final_image = self._add_legend(cropped)
        final_image.save(path)
        messagebox.showinfo("Succes", f"Imaginea adnotata a fost salvata in:\n{path}")

    def _crop_to_areas(self, annotated):
        """Decupeaza imaginea la conturul desenului principal (vezi
        _detect_drawing_bbox) UNIT cu conturul zonelor marcate, plus o
        margine de context - in loc sa pastram toata pagina bruta. Multe
        PDF-uri au mult spatiu gol si alte elemente separate de desenul
        propriu-zis (tabele, sageti, alte detalii), ceea ce facea legenda sa
        para "intr-un colt", minuscula si disproportionata fata de desen.
        Unim cu zonele marcate (nu doar desenul detectat) ca sa garantam ca
        nicio problema marcata nu ramane in afara cadrului, chiar daca
        detectia automata a desenului ar rata ceva."""
        xs0 = [a["original_coords"][0] for a in self.areas]
        ys0 = [a["original_coords"][1] for a in self.areas]
        xs1 = [a["original_coords"][2] for a in self.areas]
        ys1 = [a["original_coords"][3] for a in self.areas]
        x0, y0, x1, y1 = min(xs0), min(ys0), max(xs1), max(ys1)

        drawing_bbox = self._detect_drawing_bbox()
        if drawing_bbox is not None:
            dx0, dy0, dx1, dy1 = drawing_bbox
            x0 = min(x0, dx0)
            y0 = min(y0, dy0)
            x1 = max(x1, dx1)
            y1 = max(y1, dy1)

        pad_x = max(60, round((x1 - x0) * 0.04))
        pad_y = max(60, round((y1 - y0) * 0.04))

        img_w, img_h = annotated.size
        crop_x0 = max(0, round(x0 - pad_x))
        crop_y0 = max(0, round(y0 - pad_y))
        crop_x1 = min(img_w, round(x1 + pad_x))
        crop_y1 = min(img_h, round(y1 + pad_y))

        return annotated.crop((crop_x0, crop_y0, crop_x1, crop_y1))

    def _detect_drawing_bbox(self):
        """Detecteaza automat conturul (bounding box) desenului principal
        din imagine - grupul cel mai mare de continut (linii, hasuri,
        culori), distinct de elemente izolate mici de pe aceeasi pagina
        (tabele, sageti, alte detalii separate spatial). Multe PDF-uri de
        plan au o pagina mult mai mare decat desenul propriu-zis, cu alte
        tabele/detalii imprastiate separat - fara aceasta detectie, imaginea
        salvata ar include tot spatiul gol si elementele nelegate de desen.

        Ruleaza pe o varianta MULT redusa a imaginii (nu pe rasterul
        original, care poate avea sute de milioane de pixeli), ca sa ramana
        rapid chiar fara numpy - foloseste doar PIL. Rezultatul (bounding
        box) e scalat inapoi la rezolutia reala. Cacheaza rezultatul, ca
        exporturi repetate in aceeasi sesiune sa nu repete detectia.
        Returneaza None daca imaginea e complet alba (nimic de detectat)."""
        if self._drawing_bbox_computed:
            return self._cached_drawing_bbox

        max_dim = 500
        w, h = self.original_image.size
        scale = min(1.0, max_dim / max(w, h))
        small_w = max(1, round(w * scale))
        small_h = max(1, round(h * scale))
        small = self.original_image.resize((small_w, small_h), Image.BILINEAR)
        px = small.load()

        def is_background(r, g, b):
            return r > 245 and g > 245 and b > 245

        visited = bytearray(small_w * small_h)
        components = []  # fiecare: [minx, miny, maxx, maxy, arie]

        for sy in range(small_h):
            row_base = sy * small_w
            for sx in range(small_w):
                idx0 = row_base + sx
                if visited[idx0]:
                    continue
                visited[idx0] = 1
                r, g, b = px[sx, sy]
                if is_background(r, g, b):
                    continue
                # flood-fill (BFS/DFS cu stiva) pentru componenta curenta
                stack = [(sx, sy)]
                minx = maxx = sx
                miny = maxy = sy
                area = 0
                while stack:
                    x, y = stack.pop()
                    area += 1
                    if x < minx:
                        minx = x
                    elif x > maxx:
                        maxx = x
                    if y < miny:
                        miny = y
                    elif y > maxy:
                        maxy = y
                    for nx, ny in ((x - 1, y), (x + 1, y), (x, y - 1), (x, y + 1)):
                        if 0 <= nx < small_w and 0 <= ny < small_h:
                            nidx = ny * small_w + nx
                            if not visited[nidx]:
                                visited[nidx] = 1
                                nr, ng, nb = px[nx, ny]
                                if not is_background(nr, ng, nb):
                                    stack.append((nx, ny))
                components.append([minx, miny, maxx, maxy, area])

        if not components:
            self._cached_drawing_bbox = None
            self._drawing_bbox_computed = True
            return None

        # unim componentele apropiate spatial - un desen mare are adesea
        # goluri interne (la intersectii, rotonde, capete de linii), care
        # altfel l-ar rupe in "insule" separate - dar pastram elementele CU
        # ADEVARAT departate (tabele, alte detalii) in grupuri separate
        merge_margin = max(3, round(max(small_w, small_h) * 0.03))
        n = len(components)
        parent = list(range(n))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i

        def union(i, j):
            ri, rj = find(i), find(j)
            if ri != rj:
                parent[ri] = rj

        for i in range(n):
            ax0 = components[i][0] - merge_margin
            ay0 = components[i][1] - merge_margin
            ax1 = components[i][2] + merge_margin
            ay1 = components[i][3] + merge_margin
            for j in range(i + 1, n):
                bx0, by0, bx1, by1 = components[j][:4]
                if not (ax1 < bx0 or bx1 < ax0 or ay1 < by0 or by1 < ay0):
                    union(i, j)

        groups = {}
        for i in range(n):
            groups.setdefault(find(i), []).append(components[i])

        best_bbox = None
        best_area = 0
        for members in groups.values():
            total_area = sum(c[4] for c in members)
            if total_area > best_area:
                best_area = total_area
                best_bbox = (
                    min(c[0] for c in members),
                    min(c[1] for c in members),
                    max(c[2] for c in members),
                    max(c[3] for c in members),
                )

        minx, miny, maxx, maxy = best_bbox
        result = (minx / scale, miny / scale, (maxx + 1) / scale, (maxy + 1) / scale)
        self._cached_drawing_bbox = result
        self._drawing_bbox_computed = True
        return result

    def _add_legend(self, annotated):
        """Adauga DEASUPRA imaginii adnotate o legenda cu descrierea fiecarei
        probleme marcate (#id: descriere), ca informatia sa ramana vizibila
        si in afara aplicatiei (nu doar in panoul lateral din interfata).
        Deasupra (nu dedesubt) ca sa fie primul lucru vizibil la deschiderea
        fisierului, fara sa fie nevoie sa derulezi pe langa un desen foarte
        mare/inalt ca sa ajungi la ea."""
        img_w, img_h = annotated.size

        try:
            header_font = ImageFont.truetype("DejaVuSans-Bold.ttf", 26)
            id_font = ImageFont.truetype("DejaVuSans-Bold.ttf", 18)
            text_font = ImageFont.truetype("DejaVuSans.ttf", 18)
        except Exception:
            header_font = id_font = text_font = ImageFont.load_default()

        margin = 24
        line_spacing = 6
        entry_spacing = 16
        max_text_width = img_w - margin * 2

        measurer = ImageDraw.Draw(annotated)

        header_text = "Legenda probleme identificate"
        header_bbox = measurer.textbbox((0, 0), header_text, font=header_font)
        header_h = header_bbox[3] - header_bbox[1]

        line_bbox = measurer.textbbox((0, 0), "Ag", font=text_font)
        line_h = line_bbox[3] - line_bbox[1]

        entries = []
        for area in sorted(self.areas, key=lambda a: a["id"]):
            id_text = f"#{area['id']}"
            id_bbox = measurer.textbbox((0, 0), id_text, font=id_font)
            id_w = id_bbox[2] - id_bbox[0]
            wrap_width = max(60, max_text_width - id_w - 10)
            wrapped = self._wrap_text_lines(measurer, area["description"], text_font, wrap_width)
            entries.append((id_text, id_w, wrapped or [""]))

        legend_h = margin + header_h + margin
        for _, _, wrapped in entries:
            legend_h += len(wrapped) * (line_h + line_spacing) + entry_spacing
        legend_h += margin

        final_img = Image.new("RGB", (img_w, legend_h + img_h), "white")
        final_img.paste(annotated, (0, legend_h))
        draw = ImageDraw.Draw(final_img)

        y = margin
        draw.text((margin, y), header_text, fill="black", font=header_font)
        y += header_h + margin

        for id_text, id_w, wrapped in entries:
            draw.text((margin, y), id_text, fill="red", font=id_font)
            text_x = margin + id_w + 10
            for line in wrapped:
                draw.text((text_x, y), line, fill="black", font=text_font)
                y += line_h + line_spacing
            y += entry_spacing

        return final_img

    @staticmethod
    def _wrap_text_lines(draw, text, font, max_width):
        """Imparte textul in linii care incap in max_width pixeli la fontul
        dat, pastrand liniile explicite (\\n) din text si impartind pe
        cuvinte cele prea lungi ca sa incapa pe latimea imaginii."""
        lines = []
        for raw_line in text.splitlines() or [""]:
            words = raw_line.split(" ")
            current = ""
            for word in words:
                candidate = (current + " " + word).strip()
                bbox = draw.textbbox((0, 0), candidate, font=font)
                width = bbox[2] - bbox[0]
                if width <= max_width or not current:
                    current = candidate
                else:
                    lines.append(current)
                    current = word
            lines.append(current)
        return lines


def choose_image_path():
    if DEFAULT_IMAGE_PATH and os.path.isfile(DEFAULT_IMAGE_PATH):
        return DEFAULT_IMAGE_PATH

    root = tk.Tk()
    root.withdraw()
    path = filedialog.askopenfilename(
        title="Selecteaza imaginea sau PDF-ul planului",
        filetypes=[
            ("Imagini si PDF", "*.png *.jpg *.jpeg *.bmp *.gif *.pdf"),
            ("Imagini", "*.png *.jpg *.jpeg *.bmp *.gif"),
            ("PDF", "*.pdf"),
            ("Toate fisierele", "*.*"),
        ],
    )
    root.destroy()
    return path


def main():
    image_path = choose_image_path()
    if not image_path:
        print("Nu s-a selectat nicio imagine. Iesire.")
        return

    root = tk.Tk()
    # incarcarea fisierului e acum asincrona (vezi ProblemAreaSelector - arata
    # singura un ecran de "Se incarca..." si isi gestioneaza propriile erori,
    # inclusiv distrugerea ferestrei daca fisierul nu poate fi citit)
    app = ProblemAreaSelector(root, image_path)
    root.mainloop()


if __name__ == "__main__":
    main()