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
import os
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk
from PIL import Image, ImageTk, ImageDraw, ImageFont

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

# La cate DPI randam pagina PDF-ului (mai mare = mai clar, dar mai lent)
PDF_RENDER_DPI = 300


def load_image_from_path(path):
    """Incarca o imagine dintr-un fisier, acceptand atat imagini clasice
    (png/jpg/etc) cat si PDF (randeaza prima pagina).

    Returneaza (imagine_baza, pdf_page) - pdf_page e None daca fisierul nu
    e PDF. Cand e PDF, pastram pagina deschisa ca sa o putem rerandeaza
    direct din datele vectoriale la orice nivel de zoom (claritate maxima,
    ca in AutoCAD), in loc sa maream un raster deja facut.
    """
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
        zoom = PDF_RENDER_DPI / 72  # 72 dpi e rezolutia implicita PDF
        matrix = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=matrix)
        image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
        # NU inchidem documentul - il pastram ca sa putem rerandeaza direct
        # din datele vectoriale la orice nivel de zoom.
        return image, page

    return Image.open(path).convert("RGB"), None


class ProblemAreaSelector:

    MIN_ZOOM = 0.2
    MAX_ZOOM = 20.0
    ZOOM_STEP_IN = 1.25
    ZOOM_STEP_OUT = 0.8

    # Cat de mult mai mare randam bitmap-ul de fundal fata de viewport-ul
    # vizibil (2.0 = 100% in plus pe fiecare dimensiune). Acest "buffer" in
    # jurul zonei vizibile face ca o panoramare rapida sa nu iasa imediat
    # in zona gri neandata - ai ceva "rezerva" de imagine deja randata
    # pana vine urmatoarea randare de calitate.
    OVERSCAN = 2.0

    # La cel mult atatea secunde una de alta, lansam o randare de calitate
    # chiar daca interactiunea (drag/scroll/zoom) e inca in desfasurare - nu
    # asteptam neaparat sa se opreasca mouse-ul. Fara asta, un pan/scroll
    # continuu si lung reseteaza mereu debounce-ul si bufferul OVERSCAN nu se
    # mai reimprospateaza deloc pana la eliberarea mouse-ului, ceea ce e
    # motivul principal pentru care apare zona gri la miscari mari.
    RENDER_THROTTLE_INTERVAL = 0.15

    def __init__(self, root, image_path):
        self.root = root
        self.root.title("Selector zone cu probleme - " + os.path.basename(image_path))

        self.image_path = image_path
        self.original_image, self.pdf_page = load_image_from_path(image_path)

        self.base_scale = self._compute_fit_scale(self.original_image.size)
        self.zoom_factor = 1.0
        self.scale = self.base_scale * self.zoom_factor
        self.tk_image = None

        # Coltul din stanga-sus al zonei vizibile, in coordonate ale
        # imaginii ORIGINALE (nu scalate). Impreuna cu self.scale, defineste
        # exact ce portiune din imagine se vede in viewport.
        self.view_x = 0.0
        self.view_y = 0.0

        # Pentru debounce: randarea grea (crop+resize sau rerandare PDF) nu
        # se face la fiecare eveniment de mouse, ci e amanata putin, ca sa
        # nu se blocheze aplicatia la miscari/scroll rapide.
        self._pending_bg_render_id = None

        # Ultimul bitmap randat "de calitate" + zona (in coordonate imagine
        # originala) si scala la care a fost randat. Folosit pentru un
        # preview INSTANT la zoom: intindem/micsoram acest bitmap deja
        # existent (rapid, e mic) cat asteptam randarea de calitate reala.
        self._last_bitmap = None
        self._last_bitmap_crop = None
        self._last_bitmap_render_scale = None

        # Randarea grea (crop+resize sau rerandare PDF) ruleaza pe un thread
        # separat, ca sa nu blocheze interfata. Aceste flag-uri asigura ca
        # nu pornim niciodata doua randari simultan (fitz nu e sigur de
        # folosit din mai multe threaduri deodata) - daca vine o cerere noua
        # cat una e in curs, doar o marcam "dirty" si o reluam imediat dupa.
        self._render_busy = False
        self._render_dirty = False
        # Momentul (time.monotonic) la care a fost lansata ultima randare de
        # calitate - folosit pentru throttle in _request_bg_render().
        self._last_render_launch_time = None

        # Lista de zone. Fiecare element e un dict cu:
        #   id, description, original_coords [x0,y0,x1,y1] in imaginea originala
        self.areas = []
        self._next_id = 1

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
        w, h = size
        scale_w = VIEWPORT_WIDTH / w
        scale_h = VIEWPORT_HEIGHT / h
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
        acopera viewport-ul la zoom-ul curent."""
        return VIEWPORT_WIDTH / self.scale, VIEWPORT_HEIGHT / self.scale

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

    def _capture_crop_params(self):
        """Calculeaza zona (in coordonate imagine originala) care trebuie
        randata, incluzand marginea OVERSCAN, plus scala curenta - tot ce
        e nevoie pentru a produce bitmap-ul, capturat ca o "poza" a starii
        curente (sigur de trecut si intr-un thread de fundal)."""
        w, h = self.original_image.size
        visible_w, visible_h = self._visible_size_in_original()

        margin_w = visible_w * (self.OVERSCAN - 1) / 2
        margin_h = visible_h * (self.OVERSCAN - 1) / 2

        crop_x0 = max(0.0, self.view_x - margin_w)
        crop_y0 = max(0.0, self.view_y - margin_h)
        crop_x1 = min(w, self.view_x + visible_w + margin_w)
        crop_y1 = min(h, self.view_y + visible_h + margin_h)

        return {"crop": (crop_x0, crop_y0, crop_x1, crop_y1), "scale": self.scale}

    def _produce_bitmap(self, crop_params):
        """Partea scumpa, dar PURA (nu atinge self.view_x/self.scale/canvas):
        produce bitmap-ul PIL pentru crop_params dati. Poate fi apelata direct
        (randare sincrona) sau dintr-un thread de fundal (randare asincrona),
        pentru ca nu modifica nicio stare comuna in timp ce ruleaza."""
        crop_x0, crop_y0, crop_x1, crop_y1 = crop_params["crop"]
        scale = crop_params["scale"]

        if self.pdf_page is not None:
            return self._render_pdf_crop(crop_x0, crop_y0, crop_x1, crop_y1, scale)

        crop = self.original_image.crop(
            (int(crop_x0), int(crop_y0), int(round(crop_x1)), int(round(crop_y1)))
        )
        target_w = max(1, round((crop_x1 - crop_x0) * scale))
        target_h = max(1, round((crop_y1 - crop_y0) * scale))
        return crop.resize((target_w, target_h), Image.LANCZOS)

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
        originale - sa cada exact unde trebuie fata de view-ul curent."""
        self.tk_image = ImageTk.PhotoImage(pil_image)

        offset_x = (crop_x0 - self.view_x) * self.scale
        offset_y = (crop_y0 - self.view_y) * self.scale

        self.canvas.delete("bg")
        self.canvas.create_image(offset_x, offset_y, anchor=tk.NW, image=self.tk_image, tags="bg")
        self.canvas.tag_lower("bg")

    def _request_bg_render(self, delay=80):
        """Amana randarea grea cu `delay` ms. Daca se cere din nou inainte
        sa treaca timpul, anuleaza cererea veche - deci in timpul unui
        drag/scroll continuu nu se face o randare la fiecare eveniment de
        mouse (asta rezolva blocajele).

        Insa nu e un debounce "pur": daca a trecut deja
        RENDER_THROTTLE_INTERVAL de la ultima randare lansata, pornim una
        ACUM, nu asteptam sa se opreasca de tot interactiunea. Altfel, la un
        drag/scroll continuu si lung (multa suprafata parcursa), timer-ul de
        debounce s-ar reseta la nesfarsit si bufferul OVERSCAN nu s-ar mai
        reimprospata deloc pana la eliberarea mouse-ului - exact motivul
        pentru care apare zona gri si senzatia de lag la miscari mari."""
        if self._pending_bg_render_id is not None:
            self.root.after_cancel(self._pending_bg_render_id)
            self._pending_bg_render_id = None

        now = time.monotonic()
        if (
            self._last_render_launch_time is not None
            and (now - self._last_render_launch_time) < self.RENDER_THROTTLE_INTERVAL
        ):
            self._pending_bg_render_id = self.root.after(delay, self._do_scheduled_bg_render)
        else:
            self._do_scheduled_bg_render()

    def _do_scheduled_bg_render(self):
        self._pending_bg_render_id = None
        self._clamp_view()
        self._update_ui_state()
        self._launch_bg_render()

    def _launch_bg_render(self):
        """Porneste randarea grea PE UN THREAD SEPARAT, ca sa nu blocheze
        deloc interfata (asta era motivul pentru care aplicatia "ingheta"
        vizibil la zoom mare + panoramare mare: randarea sincrona putea dura
        sute de milisecunde, timp in care fereastra nu raspundea deloc).

        Se ruleaza un singur randare o data - daca vine o cerere noua cat
        timp una e deja in curs, nu pornim un al doilea thread (fitz/PyMuPDF
        nu e sigur de folosit din doua threaduri simultan), ci doar marcam
        ca mai trebuie o randare, care porneste imediat ce se termina cea
        curenta, cu parametrii cei mai recenti."""
        self._last_render_launch_time = time.monotonic()

        if self._render_busy:
            self._render_dirty = True
            return

        self._render_busy = True
        self._render_dirty = False
        crop_params = self._capture_crop_params()
        thread = threading.Thread(
            target=self._bg_render_worker, args=(crop_params,), daemon=True
        )
        thread.start()

    def _bg_render_worker(self, crop_params):
        """Ruleaza PE THREAD-UL DE FUNDAL. Nu atinge widget-uri Tkinter direct
        (nu e permis din alt thread) - doar calculeaza bitmap-ul, apoi preda
        rezultatul inapoi firului principal prin root.after()."""
        try:
            resized = self._produce_bitmap(crop_params)
        except Exception:
            resized = None
        self.root.after(0, self._on_bg_render_done, resized, crop_params)

    def _on_bg_render_done(self, resized, crop_params):
        """Ruleaza pe firul principal (via root.after), deci poate atinge
        canvas-ul in siguranta."""
        self._render_busy = False
        if resized is not None:
            self._apply_bitmap_result(resized, crop_params)

        if self._render_dirty:
            self._render_dirty = False
            self._launch_bg_render()

    # DPI maxim la care randam efectiv din PDF. Peste zoom-uri foarte mari,
    # randam la acest plafon si doar maream putin rezultatul (PIL), ca sa nu
    # incarcam fitz cu randari extrem de costisitoare care ar bloca aplicatia.
    MAX_EFFECTIVE_DPI = 2400

    def _render_pdf_crop(self, crop_x0, crop_y0, crop_x1, crop_y1, scale):
        """Randeaza direct din PDF (fitz) doar zona ceruta, la rezolutia
        corespunzatoare parametrului `scale` (plafonata la MAX_EFFECTIVE_DPI).
        crop_* sunt in coordonate 'pixel de baza' (spatiul lui original_image,
        la PDF_RENDER_DPI). `scale` se primeste explicit (nu se citeste
        self.scale) ca sa fie sigur de apelat dintr-un thread de fundal, fara
        sa depinda de o valoare care s-ar putea schimba intre timp pe firul
        principal."""
        pt_ratio = PDF_RENDER_DPI / 72  # pixeli-de-baza per punct PDF

        pt_x0 = crop_x0 / pt_ratio
        pt_y0 = crop_y0 / pt_ratio
        pt_x1 = crop_x1 / pt_ratio
        pt_y1 = crop_y1 / pt_ratio

        if pt_x1 <= pt_x0 or pt_y1 <= pt_y0:
            return Image.new("RGB", (1, 1), "white")

        target_w = max(1, round((crop_x1 - crop_x0) * scale))
        target_h = max(1, round((crop_y1 - crop_y0) * scale))

        effective_dpi = scale * PDF_RENDER_DPI
        capped_dpi = min(effective_dpi, self.MAX_EFFECTIVE_DPI)

        zoom = capped_dpi / 72
        matrix = fitz.Matrix(zoom, zoom)
        clip = fitz.Rect(pt_x0, pt_y0, pt_x1, pt_y1)

        pix = self.pdf_page.get_pixmap(matrix=matrix, clip=clip)
        image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)

        if capped_dpi < effective_dpi:
            image = image.resize((target_w, target_h), Image.LANCZOS)

        return image

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
            widget_x = VIEWPORT_WIDTH / 2
            widget_y = VIEWPORT_HEIGHT / 2

        # punctul din imaginea originala aflat sub cursor, ca sa ramana
        # fix pe ecran dupa schimbarea zoom-ului (zoom centrat pe cursor)
        orig_x, orig_y = self.widget_to_original(widget_x, widget_y)

        self.zoom_factor = new_zoom
        self.scale = self.base_scale * self.zoom_factor

        self.view_x = orig_x - widget_x / self.scale
        self.view_y = orig_y - widget_y / self.scale
        self._clamp_view()

        # feedback ieftin si instantaneu (pozitii, procent zoom, scrollbar);
        # randarea grea (crop/resize sau rerandare PDF) e amanata, ca sa nu
        # se blocheze aplicatia daca dai scroll rapid de mai multe ori la rand
        self._update_ui_state()
        self._show_zoom_preview()
        self._request_bg_render(delay=100)

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

        # randarea de calitate (crop/resize sau rerandare PDF) e amanata;
        # daca miscarea continua, cererea veche e anulata si reprogramata
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

        annotated.save(path)
        messagebox.showinfo("Succes", f"Imaginea adnotata a fost salvata in:\n{path}")


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
    try:
        app = ProblemAreaSelector(root, image_path)
    except Exception as e:
        root.withdraw()
        messagebox.showerror("Eroare la incarcarea fisierului", str(e))
        root.destroy()
        return
    root.mainloop()


if __name__ == "__main__":
    main()