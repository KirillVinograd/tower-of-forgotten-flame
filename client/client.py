
# client.py
# Онлайновый 2D-рогалик "Башня Забытого Пламени" — клиент на Pygame
import pygame
import socket
import threading
import json
import sys
import time
import math

SERVER_HOST = "79.174.82.250"
SERVER_PORT = 5000

WIDTH, HEIGHT = 1920, 1080
tile = 64
MAP_OFFSET_X = 40
MAP_OFFSET_Y = 40

# зум для области карты (уровень, игроки, враги)
ZOOM_MIN = 0.7
ZOOM_MAX = 1.2
ZOOM_STEP = 0.1
zoom_factor = 1.0  # 1.0 = обычный масштаб

MOVE_STEP = 0.15  # размер шага за один кадр при удержании клавиши

pygame.init()

def get_tile_size():
    """Текущий размер тайла с учётом зума."""
    return int(tile * zoom_factor)

def set_cursor_arrow():
    """Безопасно переключает курсор на обычную стрелку (если поддерживаются системные курсоры)."""
    try:
        pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_ARROW)
    except Exception:
        # старые версии pygame или отсутствие системных курсоров — просто игнорируем
        pass


def set_cursor_resize_horizontal():
    """Безопасно включает курсор горизонтального ресайза панели."""
    try:
        pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_SIZEWE)
    except Exception:
        # если такого курсора нет — ничего страшного
        pass

def get_scale_and_offsets(screen):
    """Возвращает (scale, offset_x, offset_y) для масштабирования кратно целому числу."""
    screen_rect = screen.get_rect()
    sw, sh = screen_rect.size

    # целочисленный масштаб, чтобы не было мыла
    scale = min(sw // WIDTH, sh // HEIGHT)
    if scale < 1:
        scale = 1

    target_w = WIDTH * scale
    target_h = HEIGHT * scale

    offset_x = (sw - target_w) // 2
    offset_y = (sh - target_h) // 2
    return scale, offset_x, offset_y


def screen_to_logical_coords(screen, mx, my):
    """Переводит координаты экрана в логические (960x540) с учётом целочисленного масштаба и отступов."""
    scale, offset_x, offset_y = get_scale_and_offsets(screen)
    lx = (mx - offset_x) / scale
    ly = (my - offset_y) / scale
    return lx, ly


def logical_x_to_screen(screen, lx):
    """Переводит логическую X-координату (960) в экранную X с учётом целочисленного масштаба и отступов."""
    scale, offset_x, _ = get_scale_and_offsets(screen)
    return int(offset_x + lx * scale)



state_lock = threading.Lock()
game_state = {
    "you": None,
    "level": None,
    "players": [],
    "messages": []
}

network_socket = None
network_running = False

# статус подключения
connect_status_msg = ""
connect_attempt_in_progress = False
connect_success = False

# выбор целей
selected_enemy_id = None
selected_ally_id = None

# эффекты атак
# элемент: {from:(fx,fy), to:(tx,ty), color:(r,g,b), start, duration, style, expires, special}
attack_effects = []

# флаг для "вошёл в дверь"
was_in_door_zone = False

CLASS_COLORS = {
    "воин": (220, 60, 60),
    "лучник": (80, 210, 80),
    "маг": (90, 180, 255),
    "хилер": (245, 220, 90),
}

# положение и перетаскивание правой панели
panel_x = MAP_OFFSET_X + tile*20 + 20
panel_dragging = False
panel_drag_mouse_start = 0.0
panel_drag_panel_start = 0.0

# сглаживание (визуальное) движения врагов
smooth_enemy_pos = {}

# камера: координаты верхнего левого угла видимой области (в тайлах)
camera_x = 0.0
camera_y = 0.0


def send_json(sock, obj):
    try:
        data = json.dumps(obj, ensure_ascii=False) + "\n"
        sock.sendall(data.encode("utf-8"))
    except Exception:
        pass


def recv_json_line(fileobj):
    line = fileobj.readline()
    if not line:
        return None
    line = line.strip()
    if not line:
        return None
    return json.loads(line)


def add_message(text):
    with state_lock:
        msgs = game_state["messages"]
        msgs.append(text)
        if len(msgs) > 50:
            del msgs[0]


def network_listener(sock, fileobj):
    global network_running
    try:
        while network_running:
            msg = recv_json_line(fileobj)
            if msg is None:
                add_message("Соединение с сервером потеряно.")
                break
            mtype = msg.get("type")
            if mtype == "welcome":
                add_message(msg.get("msg", "Добро пожаловать."))
            elif mtype == "event":
                add_message(msg.get("msg", ""))
            elif mtype == "error":
                add_message("[Ошибка] " + msg.get("msg", ""))
            elif mtype == "state":
                with state_lock:
                    game_state["you"] = msg.get("you")
                    game_state["level"] = msg.get("level")
                    game_state["players"] = msg.get("players", [])
            elif mtype == "attack":
                handle_attack_message(msg)
            else:
                add_message(str(msg))
    except Exception as e:
        add_message(f"Ошибка сети: {e}")
    finally:
        network_running = False
        try:
            sock.close()
        except Exception:
            pass


def handle_attack_message(msg):
    """Создаём красивый эффект атаки в зависимости от класса/типа."""
    fx = msg.get("from_x", 0.0)
    fy = msg.get("from_y", 0.0)
    tx = msg.get("to_x", 0.0)
    ty = msg.get("to_y", 0.0)
    special = bool(msg.get("special"))
    attacker_type = msg.get("attacker_type")
    attacker_id = msg.get("attacker_id")

    color = (255, 255, 255)
    style = "default"

    with state_lock:
        you = game_state.get("you")
        players = game_state.get("players") or []
        level = game_state.get("level") or {}
        enemies = (level.get("enemies") or []) if level else []

        # цвет и стиль для атак игроков
        if attacker_type == "player":
            cls_name = None
            if you and you.get("id") == attacker_id:
                cls_name = (you.get("class") or "").lower()
            else:
                for p in players:
                    if p.get("id") == attacker_id:
                        cls_name = (p.get("class") or "").lower()
                        break
            if cls_name:
                color = CLASS_COLORS.get(cls_name, (255, 255, 255))
                if cls_name == "воин":
                    style = "warrior_special" if special else "warrior"
                elif cls_name == "лучник":
                    style = "archer_special" if special else "archer"
                elif cls_name == "маг":
                    style = "mage_special" if special else "mage"
                elif cls_name == "хилер":
                    style = "heal"
                else:
                    style = "default"
            else:
                style = "default"
        else:
            # враги
            etype = None
            for e in enemies:
                if e.get("id") == attacker_id:
                    etype = e.get("etype")
                    break
            if etype == "melee":
                style = "enemy_melee"
            elif etype == "ranged":
                style = "enemy_ranged"
            else:
                style = "enemy"
            color = (255, 80, 80) if style == "enemy_melee" else (255, 160, 100)

    now = time.time()
    duration = 0.4 if not special else 0.6
    attack_effects.append({
        "from": (fx, fy),
        "to": (tx, ty),
        "color": color,
        "start": now,
        "duration": duration,
        "style": style,
        "expires": now + duration,
        "special": special,
        "target_type": msg.get("target_type"),
        "target_id": msg.get("target_id"),
    })


def send_command(command, **kwargs):
    global network_socket, network_running
    if not network_running or network_socket is None:
        return
    msg = {"type": "command", "command": command}
    msg.update(kwargs)
    send_json(network_socket, msg)



def apply_local_move(dx, dy):
    """Простое клиентское предсказание движения, чтобы сгладить лаги.
    Обновляем только свои координаты локально, сервер остаётся источником истины."""
    with state_lock:
        you = game_state.get("you")
        level = game_state.get("level")
        if not you or not level:
            return
        nx = you.get("x", 0.0) + dx
        ny = you.get("y", 0.0) + dy
        w = level.get("width", 20)
        h = level.get("height", 12)
        # лёгкий клип по краям карты
        if w > 0:
            nx = max(0.0, min(w - 0.001, nx))
        if h > 0:
            ny = max(0.0, min(h - 0.001, ny))
        you["x"] = nx
        you["y"] = ny


def draw_text(surface, text, x, y, font, color=(255, 255, 255)):
    if not text:
        return
    img = font.render(text, True, color)
    surface.blit(img, (x, y))


def draw_enter_name(screen, font, big_font, name_input):
    screen.fill((10, 10, 30))

    # Заголовок по центру, рассчитанный под базовое 1920x1080
    draw_text(
        screen,
        "Башня Забытого Пламени",
        WIDTH // 2 - 400,
        160,
        big_font,
        (255, 220, 0),
    )

    draw_text(
        screen,
        "Введите имя героя и нажмите Enter:",
        400,
        400,
        font,
    )

    # Поле ввода (в 2 раза шире и выше, чем было в 960x540)
    pygame.draw.rect(
        screen,
        (40, 40, 60),
        (400, 460, 1120, 80),
        border_radius=6,
    )

    draw_text(
        screen,
        name_input + "|",
        420,
        472,
        font,
        (200, 200, 255),
    )

    draw_text(
        screen,
        "Esc - выход",
        400,
        600,
        font,
        (180, 180, 180),
    )


def draw_choose_class(screen, font, big_font, idx, status_text):
    screen.fill((10, 10, 30))
    classes = ["Воин", "Лучник", "Маг", "Хилер"]
    desc = [
        "Воин: много HP, щит для команды.",
        "Лучник: высокий урон по одной цели.",
        "Маг: урон по всем врагам.",
        "Хилер: не атакует, лечит союзников.",
    ]

    # Текст-инструкция
    draw_text(
        screen,
        "Выберите класс стрелками и нажмите Enter",
        300,
        240,
        font,
    )

    # Список классов
    for i, name in enumerate(classes):
        y = 400 + i * 120  # было 200 + i * 60
        color = (255, 255, 0) if i == idx else (220, 220, 220)

        draw_text(screen, name, 440, y, big_font, color)
        draw_text(screen, desc[i], 440, y + 60, font, (200, 200, 200))

    draw_text(screen, "Esc - выход", 400, 880, font, (180, 180, 180))

    if status_text:
        draw_text(screen, status_text, 300, 940, font, (255, 120, 120))



def draw_bar(surface, x, y, w, h, value, max_value, fg_color, bg_color=(60, 60, 60)):
    pygame.draw.rect(surface, bg_color, (x, y, w, h))
    if max_value and value > 0:
        fill = max(0, min(w, int(w * value / max_value)))
        pygame.draw.rect(surface, fg_color, (x, y, fill, h))


def draw_attack_effects(screen, effects, you, players, enemies):
    now = time.time()
    still = []
    tile = get_tile_size()
    global camera_x, camera_y

    for eff in effects:
        if eff["expires"] <= now:
            continue
        still.append(eff)
        fx, fy = eff["from"]
        tx, ty = eff["to"]
        sx = MAP_OFFSET_X + (fx - camera_x) * tile + tile // 2
        sy = MAP_OFFSET_Y + (fy - camera_y) * tile + tile // 2
        ex = MAP_OFFSET_X + (tx - camera_x) * tile + tile // 2
        ey = MAP_OFFSET_Y + (ty - camera_y) * tile + tile // 2
        color = eff["color"]
        style = eff.get("style", "default")
        start = eff.get("start", now - 0.1)
        duration = eff.get("duration", 0.4)
        t = (now - start) / duration
        if t < 0.0:
            t = 0.0
        if t > 1.0:
            t = 1.0

        dx = ex - sx
        dy = ey - sy
        dist = math.hypot(dx, dy) or 1.0
        nx = dx / dist
        ny = dy / dist

        # Перпендикуляр
        px = -ny
        py = nx

        if style in ("warrior", "warrior_special"):
            # Три параллельных "разреза" у цели
            length = 24 + (6 if style == "warrior_special" else 0)
            width = 3 if style == "warrior" else 4
            # центр немного перед целью (в сторону атакующего)
            cx = ex - nx * 10
            cy = ey - ny * 10
            offset = 5
            for i in (-1, 0, 1):
                ox = px * offset * i
                oy = py * offset * i
                x1 = cx - nx * length / 2 + ox
                y1 = cy - ny * length / 2 + oy
                x2 = cx + nx * length / 2 + ox
                y2 = cy + ny * length / 2 + oy
                pygame.draw.line(screen, color, (x1, y1), (x2, y2), width)
        elif style in ("archer", "archer_special"):
            # Самонаводящаяся стрела (как снаряды врагов)
            tx_dyn, ty_dyn = tx, ty
            target_type = eff.get("target_type")
            target_id = eff.get("target_id")
            if target_type == "enemy" and target_id is not None:
                for en in enemies:
                    if en.get("id") == target_id:
                        tx_dyn = en.get("x", tx_dyn)
                        ty_dyn = en.get("y", ty_dyn)
                        break
            elif target_type == "player" and target_id is not None:
                if you and you.get("id") == target_id:
                    tx_dyn = you.get("x", tx_dyn)
                    ty_dyn = you.get("y", ty_dyn)
                else:
                    for pl in players:
                        if pl.get("id") == target_id:
                            tx_dyn = pl.get("x", tx_dyn)
                            ty_dyn = pl.get("y", ty_dyn)
                            break

            ex = MAP_OFFSET_X + tx_dyn * tile + tile // 2
            ey = MAP_OFFSET_Y + ty_dyn * tile + tile // 2

            dx = ex - sx
            dy = ey - sy
            dist = math.hypot(dx, dy) or 1.0
            nx = dx / dist
            ny = dy / dist
            px = -ny
            py = nx

            # позиция наконечника
            tip_x = sx + dx * t
            tip_y = sy + dy * t

            # УВЕЛИЧЕННАЯ стрела
            shaft_width = 3 if style == "archer" else 4
            pygame.draw.line(screen, color, (sx, sy), (tip_x, tip_y), shaft_width)

            head_len = 16
            head_side = 8
            back_x = tip_x - nx * head_len
            back_y = tip_y - ny * head_len
            left_x = back_x + px * head_side
            left_y = back_y + py * head_side
            right_x = back_x - px * head_side
            right_y = back_y - py * head_side
            pygame.draw.polygon(screen, color, [(tip_x, tip_y), (left_x, left_y), (right_x, right_y)])
        elif style in ("mage", "mage_special"):
            cur_x = sx + dx * t
            cur_y = sy + dy * t
            main_color = color
            bright_color = (
                min(255, main_color[0] + 60),
                min(255, main_color[1] + 60),
                min(255, main_color[2] + 60),
            )
            width_outer = 8 if style == "mage_special" else 6
            width_inner = 4 if style == "mage_special" else 3
            pygame.draw.line(screen, main_color, (sx, sy), (cur_x, cur_y), width_outer)
            pygame.draw.line(screen, bright_color, (sx, sy), (cur_x, cur_y), width_inner)
        elif style == "heal":
            # Лечащий луч и пульсирующий круг на цели
            heal_color = (120, 255, 160)
            cur_x = sx + dx * t
            cur_y = sy + dy * t
            pygame.draw.line(screen, heal_color, (sx, sy), (cur_x, cur_y), 4)
            # пульсация
            radius = 8 + int(8 * (1.0 - t))
            pygame.draw.circle(screen, heal_color, (int(ex), int(ey)), max(3, radius), 2)
        elif style in ("enemy_melee", "enemy_ranged", "enemy"):
            if style == "enemy_melee":
                # короткий жёсткий удар
                length = 18
                cx = ex - nx * 6
                cy = ey - ny * 6
                x1 = cx - nx * length / 2
                y1 = cy - ny * length / 2
                x2 = cx + nx * length / 2
                y2 = cy + ny * length / 2
                pygame.draw.line(screen, color, (x1, y1), (x2, y2), 4)
            else:
                # летающий снаряд: цель обновляется каждый кадр (самонаводящийся снаряд)
                tx_dyn, ty_dyn = tx, ty
                target_type = eff.get("target_type")
                target_id = eff.get("target_id")
                if target_type == "player" and target_id is not None:
                    if you and you.get("id") == target_id:
                        tx_dyn = you.get("x", tx_dyn)
                        ty_dyn = you.get("y", ty_dyn)
                    else:
                        for pl in players:
                            if pl.get("id") == target_id:
                                tx_dyn = pl.get("x", tx_dyn)
                                ty_dyn = pl.get("y", ty_dyn)
                                break
                ex_dyn = MAP_OFFSET_X + (tx_dyn - camera_x) * tile + tile // 2
                ey_dyn = MAP_OFFSET_Y + (ty_dyn - camera_y) * tile + tile // 2
                dx_dyn = ex_dyn - sx
                dy_dyn = ey_dyn - sy

                dist_dyn = math.hypot(dx_dyn, dy_dyn) or 1.0
                nx_dyn = dx_dyn / dist_dyn
                ny_dyn = dy_dyn / dist_dyn
                bx = sx + dx_dyn * t
                by = sy + dy_dyn * t
                # УВЕЛИЧЕННЫЙ снаряд врага
                pygame.draw.circle(screen, color, (int(bx), int(by)), 10)
        else:
            # базовая линия
            width = 3 if eff.get("special") else 2
            pygame.draw.line(screen, color, (sx, sy), (ex, ey), width)

    return still



def draw_game(screen, font, small_font):
    screen.fill((5, 5, 25))
    tile = get_tile_size()
    with state_lock:
        you = game_state["you"]
        level = game_state["level"]
        players = list(game_state["players"])
        messages = list(game_state["messages"])
        effects_copy = list(attack_effects)

    # если ещё нет данных от сервера — просто пишем сообщение и выходим
    if you is None or level is None:
        draw_text(screen, "Ожидание данных от сервера...", 260, HEIGHT // 2, font, (255, 255, 255))
        return

    # --- обновляем камеру, чтобы она следовала за героем ---
    global camera_x, camera_y
    level_width = level.get("width", 20)
    level_height = level.get("height", 12)

    # размер видимой области в тайлах (как и было: 20x12)
    VIEW_W_TILES = 20
    VIEW_H_TILES = 12

    # целевая позиция камеры, чтобы герой был примерно в центре экрана
    target_x = you["x"] + 0.5 - VIEW_W_TILES / 2
    target_y = you["y"] + 0.5 - VIEW_H_TILES / 2

    # ограничиваем камеру границами карты
    max_cam_x = max(0.0, level_width - VIEW_W_TILES)
    max_cam_y = max(0.0, level_height - VIEW_H_TILES)

    if target_x < 0.0:
        target_x = 0.0
    if target_y < 0.0:
        target_y = 0.0
    if target_x > max_cam_x:
        target_x = max_cam_x
    if target_y > max_cam_y:
        target_y = max_cam_y

    # плавное движение камеры
    lerp = 0.25  # если покажется слишком резко/медленно — можно потом подправить
    camera_x += (target_x - camera_x) * lerp
    camera_y += (target_y - camera_y) * lerp

    # левая часть — карта (видимая область 20x12 тайлов)
    map_rect = pygame.Rect(MAP_OFFSET_X, MAP_OFFSET_Y, tile * VIEW_W_TILES, tile * VIEW_H_TILES)
    pygame.draw.rect(screen, (20, 20, 40), map_rect)

    # --- сетка, привязанная к мировой карте и камере ---
    # вертикальные линии
    start_x = int(camera_x)
    end_x = int(camera_x + VIEW_W_TILES) + 1
    if end_x > level_width:
        end_x = level_width
    for gx in range(start_x, end_x + 1):
        sx = MAP_OFFSET_X + (gx - camera_x) * tile
        pygame.draw.line(
            screen, (30, 30, 60),
            (sx, MAP_OFFSET_Y),
            (sx, MAP_OFFSET_Y + VIEW_H_TILES * tile)
        )

    # горизонтальные линии
    start_y = int(camera_y)
    end_y = int(camera_y + VIEW_H_TILES) + 1
    if end_y > level_height:
        end_y = level_height
    for gy in range(start_y, end_y + 1):
        sy = MAP_OFFSET_Y + (gy - camera_y) * tile
        pygame.draw.line(
            screen, (30, 30, 60),
            (MAP_OFFSET_X, sy),
            (MAP_OFFSET_X + VIEW_W_TILES * tile, sy)
        )

    global selected_enemy_id, selected_ally_id

    enemies = level.get("enemies", []) or []
    door = (level.get("door") or {})
    shield_active = level.get("shield_active", False)

    # дверь
    if door.get("open") and door.get("x") is not None:
        dx = door["x"]
        dy = door["y"]
        rect = pygame.Rect(
            MAP_OFFSET_X + (dx - camera_x) * tile + 8,
            MAP_OFFSET_Y + (dy - camera_y) * tile + 8,
            tile - 16,
            tile - 16
        )
        pygame.draw.rect(screen, (230, 200, 40), rect)
        pygame.draw.rect(screen, (0, 0, 0), rect, 2)


    # опасные зоны уровня (hazards) — круги, телеграфы и т.п.
    hazards = level.get("hazards") or []
    now_t = time.time()

    for h in hazards:
        h_type = h.get("type")
        if h_type == "boss10_spawn":
            hx = float(h.get("x", 0.0))
            hy = float(h.get("y", 0.0))
            radius_tiles = float(h.get("radius", 0.0))
            start_t = float(h.get("start_time", h.get("start", now_t)))

            # центр круга в пикселях
            cx = int(MAP_OFFSET_X + (hx - camera_x) * tile + tile / 2)
            cy = int(MAP_OFFSET_Y + (hy - camera_y) * tile + tile / 2)
            radius_px = int(radius_tiles * tile)

            # простое мерцание по синусоиде
            phase = now_t - start_t
            base = 190
            amp = 50
            v = int(base + amp * math.sin(phase * 4.0))
            v = max(0, min(255, v))
            color = (50, v, 80)

            pygame.draw.circle(screen, color, (cx, cy), radius_px, width=3)


    # рисуем врагов (сглаженное движение и разные формы)
    global smooth_enemy_pos
    current_ids = set()
    for e in enemies:
        eid = e.get("id")
        current_ids.add(eid)
        ex = e.get("x", 0.0)
        ey = e.get("y", 0.0)

        # сглаживание позиции (визуальное)
        vx, vy = smooth_enemy_pos.get(eid, (ex, ey))
        alpha = 0.35  # чем выше, тем быстрее "догоняет" реальное положение
        vx += (ex - vx) * alpha
        vy += (ey - vy) * alpha
        smooth_enemy_pos[eid] = (vx, vy)

        etype = e.get("etype", "melee")
        is_boss = e.get("boss")
        is_miniboss = e.get("miniboss")

        color = (200, 50, 50)
        if is_boss:
            color = (255, 80, 0)
        elif is_miniboss:
            color = (230, 120, 40)

        # центр фигуры
        cx = MAP_OFFSET_X + (vx - camera_x) * tile + tile // 2
        cy = MAP_OFFSET_Y + (vy - camera_y) * tile + tile // 2
        base_half = (tile - 8) // 2
        half_size = base_half * (3 if is_boss else 1)

        rect = pygame.Rect(0, 0, half_size*2, half_size*2)
        rect.center = (int(cx), int(cy))

        if etype == "ranged":
            # враги-дальники — треугольники
            points = [
                (rect.centerx, rect.centery - half_size),
                (rect.centerx - half_size, rect.centery + half_size),
                (rect.centerx + half_size, rect.centery + half_size),
            ]
            pygame.draw.polygon(screen, color, points)
        else:
            # враги-ближники — квадраты
            pygame.draw.rect(screen, color, rect)

        if e.get("id") == selected_enemy_id:
            pygame.draw.rect(screen, (255, 255, 0), rect.inflate(4, 4), 2)

    # чистим позиции врагов, которые исчезли
    smooth_enemy_pos = {eid: pos for eid, pos in smooth_enemy_pos.items() if eid in current_ids}

    # рисуем игроков (разные формы)
    shield_outline_color = (120, 220, 255)
    for p in players:
        px = p.get("x", 0.0)
        py = p.get("y", 0.0)
        alive = p.get("alive", True)
        cls = (p.get("class") or "").lower()
        base_color = CLASS_COLORS.get(cls, (60, 200, 80))
        color = base_color if alive else (100, 100, 100)

        rect = pygame.Rect(
            MAP_OFFSET_X + (px - camera_x) * tile + 6,
            MAP_OFFSET_Y + (py - camera_y) * tile + 6,
            tile - 12,
            tile - 12
        )

        cx, cy = rect.center

        is_you = (you is not None and p.get("id") == you.get("id"))

        if alive:
            if cls == "воин":
                pygame.draw.rect(screen, color, rect)
            elif cls == "лучник":
                size = (tile // 2) - 4
                points = [
                    (cx, cy - size),
                    (cx - size, cy + size),
                    (cx + size, cy + size),
                ]
                pygame.draw.polygon(screen, color, points)
            elif cls in ("маг",):
                radius = (tile // 2) - 6
                pygame.draw.circle(screen, color, (cx, cy), radius)
            elif cls in ("хилер",):
                radius = (tile // 2) - 6
                pygame.draw.circle(screen, color, (cx, cy), radius)
            else:
                pygame.draw.rect(screen, color, rect)
        else:
            pygame.draw.rect(screen, color, rect)
            pygame.draw.line(screen, (50, 50, 50), rect.topleft, rect.bottomright, 2)
            pygame.draw.line(screen, (50, 50, 50), rect.topright, rect.bottomleft, 2)

        # рамка, если это вы
        if is_you:
            pygame.draw.rect(screen, (255, 255, 255), rect.inflate(4, 4), 1)

        # свечение щита
        if shield_active and alive:
            pygame.draw.rect(screen, shield_outline_color, rect.inflate(6, 6), 2)

        # имя над головой (чуть выше и по центру)
        name_img = small_font.render(p["name"], True, (220, 220, 220))
        name_rect = name_img.get_rect()
        # midbottom = центр по X, снизу — чуть выше прямоугольника персонажа
        name_rect.midbottom = (cx, rect.y - 8)
        screen.blit(name_img, name_rect.topleft)

        if p["id"] == selected_ally_id:
            pygame.draw.rect(screen, (255, 255, 0), rect.inflate(4, 4), 2)

    # эффекты атак
    new_effects = draw_attack_effects(screen, effects_copy, you, players, enemies)
    with state_lock:
        attack_effects[:] = new_effects

    # правая панель (может сдвигаться по оси X)
    global panel_x
    # небольшие ограничения, чтобы панель не уезжала слишком далеко
    min_panel_x = MAP_OFFSET_X + tile*20 // 2
    max_panel_x = WIDTH - 220
    if panel_x < min_panel_x:
        panel_x = min_panel_x
    if panel_x > max_panel_x:
        panel_x = max_panel_x

    # фон правой панели
    panel_rect = pygame.Rect(panel_x - 10, 10, WIDTH - panel_x - 10, HEIGHT - 20)
    pygame.draw.rect(screen, (15, 15, 35), panel_rect)

    # четкая вертикальная граница панели — за неё пользователь тянет
    border_rect = pygame.Rect(panel_x - 5, 10, 2, HEIGHT - 20)
    pygame.draw.rect(screen, (80, 80, 120), border_rect)

    # инфо о герое
    draw_text(screen, f"{you['name']} ({you['class']})", panel_x, 20, font, (255, 255, 0))
    loc_stage = you.get("stage", 0)
    if loc_stage == 0:
        draw_text(screen, "Локация: ХАБ", panel_x, 50, font, (200, 200, 200))
    elif loc_stage == 11:
        draw_text(screen, "Локация: Вход", panel_x, 50, font, (200, 200, 200))
    else:
        draw_text(screen, f"Уровень башни: {loc_stage}", panel_x, 50, font, (200, 200, 200))

    hp_y = 90
    mp_y = 120
    bar_w = 220
    bar_h = 20

    draw_bar(screen, panel_x, hp_y, bar_w, bar_h, you["hp"], you["max_hp"], (220, 50, 50))
    draw_text(screen, f"HP: {you['hp']}/{you['max_hp']}", panel_x, hp_y, small_font)

    draw_bar(screen, panel_x, mp_y, bar_w, bar_h, you["mana"], you["max_mana"], (50, 100, 255))
    draw_text(screen, f"MP: {you['mana']}/{you['max_mana']}", panel_x, mp_y, small_font)

    # отображаем стойку лучника, если это лучник
    stance = you.get("archer_stance", "move")
    if (you.get("class") or "").lower() == "лучник":
        stance_ru = "Движение" if stance == "move" else "Наизготовка"
        draw_text(screen, f"Стойка: {stance_ru}", panel_x, mp_y + 30, small_font, (200, 220, 255))

    draw_text(
        screen,
        f"Щит группы: {'АКТИВЕН' if shield_active else 'нет'}",
        panel_x, mp_y + 50, small_font,
        (120, 220, 120) if shield_active else (180, 180, 180)
    )

    # КД умения
    cd_total = you.get("special_cd", 0.0) or 0.0
    cd_left = you.get("special_cd_left", 0.0) or 0.0
    if cd_total > 0:
        if cd_left <= 0.01:
            draw_text(screen, "Q: спец. способность — ГОТОВА", panel_x, mp_y + 70, small_font, (200, 220, 255))
        else:
            draw_text(screen, f"Q: перезарядка {int(cd_left)} с", panel_x, mp_y + 70, small_font, (200, 200, 230))

    # таймер респавна врагов
    next_resp = level.get("next_respawn_in", 0)
    if next_resp and enemies and not shield_active:
        draw_text(screen, f"Респавн врагов через: {next_resp} с", panel_x, mp_y + 90, small_font, (220, 180, 180))
    elif next_resp and enemies:
        draw_text(screen, f"Респавн врагов через: {next_resp} с", panel_x, mp_y + 90, small_font, (220, 180, 180))

    # информация о двери
    door_y = mp_y + 115  # было 195, теперь чуть ниже

    if door.get("open"):
        draw_text(screen, "Дверь наверх: ОТКРЫТА", panel_x, door_y, small_font, (240, 220, 120))
    else:
        draw_text(screen, "Дверь наверх: закрыта", panel_x, door_y, small_font, (180, 180, 180))

    # выбранные цели
    sel_y = door_y + 25
    if selected_enemy_id is not None:
        enemy_info = None
        for e in enemies:
            if e.get("id") == selected_enemy_id:
                enemy_info = e
                break
        if enemy_info:
            etype = enemy_info.get("etype", "")
            t_str = "дальник" if etype == "ranged" else "ближник"
            draw_text(screen, "Цель (враг):", panel_x, sel_y, font, (255, 200, 200))
            draw_text(
                screen,
                f"{enemy_info['name']} [{t_str}] HP: {enemy_info['hp']}/{enemy_info['max_hp']}",
                panel_x, sel_y + 22,
                small_font, (255, 200, 200)
            )
            sel_y += 44

    if selected_ally_id is not None:
        ally = None
        for p in players:
            if p.get("id") == selected_ally_id:
                ally = p
                break
        if ally:
            draw_text(screen, "Цель (союзник):", panel_x, sel_y, font, (200, 230, 255))
            draw_text(
                screen,
                f"{ally['name']}  HP: {ally['hp']}/{ally['max_hp']}",
                panel_x, sel_y + 22,
                small_font, (200, 230, 255)
            )
            sel_y += 44

    # управление
    u_y = max(sel_y + 10, door_y + 60)
    draw_text(screen, "Управление:", panel_x, u_y, font, (200, 200, 200))

    line_h = small_font.get_height() + 10 # Расстояние между текстами
    draw_text(screen, "Удерживайте WASD / стрелки - движение", panel_x, u_y + line_h, small_font)
    draw_text(screen, "ЛКМ по врагу/союзнику - выбрать цель", panel_x, u_y + 2 * line_h, small_font)
    draw_text(screen, "SPACE - атака по выбранному врагу", panel_x, u_y + 3 * line_h, small_font)
    draw_text(screen, "Q - спец. способность (у хилера — хил)", panel_x, u_y + 4 * line_h, small_font)
    draw_text(screen, "R - воскрешение выбранного союзника", panel_x, u_y + 5 * line_h, small_font)
    draw_text(screen, "Подойдите к двери, чтобы подняться выше", panel_x, u_y + 6 * line_h, small_font)
    draw_text(screen, "TAB - обновить статус, Esc - выход", panel_x, u_y + 7 * line_h, small_font)

    # лог
    log_header_y = u_y + 8 * line_h + 10
    draw_text(screen, "События:", panel_x, log_header_y, font, (200, 200, 200))
    log_y = log_header_y + font.get_height() + 4
    log_step = small_font.get_height() + 8 # Расстояние между текстами
    for line in messages[-8:]:
        draw_text(screen, line, panel_x, log_y, small_font, (220, 220, 220))
        log_y += log_step



def handle_mouse_click(pos):
    global selected_enemy_id, selected_ally_id
    global camera_x, camera_y

    tile = get_tile_size()
    x, y = pos
    with state_lock:
        you = game_state.get("you")
        level = game_state.get("level")
        players = list(game_state.get("players") or [])
    if not level or not you:
        return
    enemies = level.get("enemies", []) or []

    # сначала ищем врага (используем те же размеры, что и при отрисовке)
    global smooth_enemy_pos
    clicked = False
    for e in enemies:
        eid = e.get("id")
        ex = e.get("x", 0.0)
        ey = e.get("y", 0.0)
        vx, vy = smooth_enemy_pos.get(eid, (ex, ey))
        is_boss = e.get("boss")
        base_half = (tile - 8) // 2
        half_size = base_half * (3 if is_boss else 1)
        cx = MAP_OFFSET_X + (vx - camera_x) * tile + tile // 2
        cy = MAP_OFFSET_Y + (vy - camera_y) * tile + tile // 2
        rect = pygame.Rect(0, 0, half_size*2, half_size*2)
        rect.center = (int(cx), int(cy))
        if rect.collidepoint(x, y):
            selected_enemy_id = e.get("id")
            selected_ally_id = None
            clicked = True
            break

    # если не враг — ищем игрока
    if not clicked:
        for p in players:
            px = p.get("x", 0.0)
            py = p.get("y", 0.0)
            rect = pygame.Rect(
                MAP_OFFSET_X + (px - camera_x) * tile + 6,
                MAP_OFFSET_Y + (py - camera_y) * tile + 6,
                tile - 12,
                tile - 12
            )
            if rect.collidepoint(x, y):
                selected_ally_id = p.get("id")
                selected_enemy_id = None
                clicked = True
                break

    if not clicked:
        selected_enemy_id = None
        selected_ally_id = None


def connect_to_server(player_name, cls_name):
    """Функция, которая запускается в отдельном потоке."""
    global network_socket, network_running, connect_status_msg, connect_attempt_in_progress, connect_success
    try:
        connect_status_msg = f"Подключение к серверу {SERVER_HOST}:{SERVER_PORT}..."
        sock = socket.create_connection((SERVER_HOST, SERVER_PORT), timeout=5)
    except Exception as e:
        connect_status_msg = f"Ошибка подключения: {e}"
        add_message(connect_status_msg)
        connect_success = False
        connect_attempt_in_progress = False
        return

    f = sock.makefile("r", encoding="utf-8")
    hello = {
        "type": "hello",
        "name": player_name,
        "class": cls_name
    }
    send_json(sock, hello)
    network_socket = sock
    network_running = True
    connect_success = True
    connect_status_msg = "Подключено. Ожидание данных от сервера..."
    t = threading.Thread(target=network_listener, args=(sock, f), daemon=True)
    t.start()
    connect_attempt_in_progress = False


def main():
    global network_running, network_socket, connect_attempt_in_progress, connect_success, connect_status_msg
    global selected_enemy_id, selected_ally_id, was_in_door_zone
    global fullscreen, panel_x, panel_dragging, panel_drag_mouse_start, panel_drag_panel_start
    global zoom_factor


    screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.RESIZABLE)
    pygame.display.set_caption("Башня Забытого Пламени")
    clock = pygame.time.Clock()

    # логическая поверхность, в неё рисуем, а потом аккуратно скейлим под окно
    game_surface = pygame.Surface((WIDTH, HEIGHT))

    # базовый курсор — стрелка
    set_cursor_arrow()



    font = pygame.font.SysFont("arial", 33)
    big_font = pygame.font.SysFont("arial", 53, bold=True)
    small_font = pygame.font.SysFont("arial", 18)


    mode = "enter_name"
    name_input = ""
    class_idx = 0
    classes = ["воин", "лучник", "маг", "хилер"]
    player_name = None
    player_class = None

    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False

            if mode == "enter_name":
                if event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key == pygame.K_RETURN:
                        if name_input.strip():
                            player_name = name_input.strip()
                            mode = "choose_class"
                    elif event.key == pygame.K_BACKSPACE:
                        name_input = name_input[:-1]
                    else:
                        if len(name_input) < 16 and event.unicode:
                            name_input += event.unicode
            elif mode == "choose_class":
                if event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key in (pygame.K_UP, pygame.K_LEFT):
                        class_idx = (class_idx - 1) % len(classes)
                    elif event.key in (pygame.K_DOWN, pygame.K_RIGHT):
                        class_idx = (class_idx + 1) % len(classes)
                    elif event.key == pygame.K_RETURN:
                        if not connect_attempt_in_progress:
                            player_class = classes[class_idx]
                            connect_status_msg = ""
                            connect_success = False
                            connect_attempt_in_progress = True
                            t = threading.Thread(
                                target=connect_to_server,
                                args=(player_name, player_class),
                                daemon=True
                            )
                            t.start()
            elif mode == "play":
                if event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key == pygame.K_SPACE:
                        # SPACE: у хилера — хил выбранного союзника, у остальных — атака по врагу
                        with state_lock:
                            you = game_state.get("you")
                        cls = (you.get("class") or "").lower() if you else ""
                        if cls in ("хилер", "хиллер", "healer"):
                            send_command("attack", target_enemy_id=None, target_player_id=selected_ally_id)
                        else:
                            send_command("attack", target_enemy_id=selected_enemy_id)
                    elif event.key == pygame.K_q:
                        send_command("special", target_player_id=selected_ally_id)
                    elif event.key == pygame.K_TAB:
                        send_command("status")
                    elif event.key == pygame.K_r:
                        if selected_ally_id is not None:
                            send_command("res", target_player_id=selected_ally_id)
                        else:
                            add_message("Сначала выберите союзника для воскрешения (клик ЛКМ).")

                elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                    mx, my = event.pos
                    # переводим координаты экрана в логические (960x540)
                    lx, ly = screen_to_logical_coords(screen, mx, my)

                    # проверяем, кликнули ли по вертикальной границе правой панели —
                    # если да, начинаем перетаскивание
                    border_rect = pygame.Rect(panel_x - 5, 10, 10, HEIGHT - 20)
                    if border_rect.collidepoint(lx, ly):
                        panel_dragging = True
                        panel_drag_mouse_start = lx
                        panel_drag_panel_start = panel_x
                    else:
                        # обычный клик по карте / игрокам / врагам
                        handle_mouse_click((lx, ly))

                elif event.type == pygame.MOUSEBUTTONUP and event.button == 1:
                    panel_dragging = False

                elif event.type == pygame.MOUSEMOTION:
                    mx, my = event.pos
                    screen_rect = screen.get_rect()

                    # --- перетаскивание правой панели ---
                    if panel_dragging:
                        lx, _ = screen_to_logical_coords(screen, mx, my)
                        dx_drag = lx - panel_drag_mouse_start
                        panel_x = int(panel_drag_panel_start + dx_drag)

                    # --- смена курсора при наведении на границу правой панели ---
                    # логическая X-координата центра полосы-границы
                    border_x_screen = logical_x_to_screen(screen, panel_x)

                    if abs(mx - border_x_screen) <= 6:
                        # курсор "можно тянуть влево-вправо"
                        set_cursor_resize_horizontal()
                    else:
                        # обычный курсор
                        set_cursor_arrow()
                
                elif event.type == pygame.MOUSEWHEEL:
                    # прокрутка вверх — приблизить, вниз — отдалить
                    zoom_factor += event.y * ZOOM_STEP
                    if zoom_factor < ZOOM_MIN:
                        zoom_factor = ZOOM_MIN
                    if zoom_factor > ZOOM_MAX:
                        zoom_factor = ZOOM_MAX




        # переключение в режим игры после успешного подключения
        if mode == "choose_class" and connect_success and network_running:
            mode = "play"

        # непрерывное движение и проверка двери
        if mode == "play":
            keys = pygame.key.get_pressed()
            dx = dy = 0.0
            if keys[pygame.K_w] or keys[pygame.K_UP]:
                dy -= 1.0
            if keys[pygame.K_s] or keys[pygame.K_DOWN]:
                dy += 1.0
            if keys[pygame.K_a] or keys[pygame.K_LEFT]:
                dx -= 1.0
            if keys[pygame.K_d] or keys[pygame.K_RIGHT]:
                dx += 1.0

            # В стойке "Наизготовка" лучник не может двигаться (даже локально)
            can_move = True
            with state_lock:
                you_local = game_state.get("you")
            if you_local:
                cls_local = (you_local.get("class") or "").lower()
                if cls_local == "лучник" and you_local.get("archer_stance", "move") == "ready":
                    can_move = False

            if can_move and (dx != 0.0 or dy != 0.0):
                length = math.hypot(dx, dy)
                if length != 0.0:
                    dx = dx / length * MOVE_STEP
                    dy = dy / length * MOVE_STEP
                    send_command("move", dx=dx, dy=dy)
                    # локально предсказываем движение для плавности
                    apply_local_move(dx, dy)


            # проверка двери
            with state_lock:
                you = game_state.get("you")
                level = game_state.get("level")
            in_zone = False
            if you and level:
                door = (level.get("door") or {})
                if door.get("open") and door.get("x") is not None:
                    dx = you["x"] - door["x"]
                    dy = you["y"] - door["y"]
                    if dx*dx + dy*dy <= 0.6*0.6:
                        in_zone = True
            if in_zone and not was_in_door_zone:
                send_command("enter_door")
            was_in_door_zone = in_zone

        # отрисовка в логическую поверхность фиксированного размера 960x540
        game_surface.fill((0, 0, 0))
        if mode == "enter_name":
            draw_enter_name(game_surface, font, big_font, name_input)
        elif mode == "choose_class":
            draw_choose_class(game_surface, font, big_font, class_idx, connect_status_msg)
        elif mode == "play":
            draw_game(game_surface, font, small_font)

        # Масштабируем кратно целому числу без потери чёткости
        scale, offset_x, offset_y = get_scale_and_offsets(screen)

        screen.fill((0, 0, 0))
        if scale == 1:
            # окно меньше или равно 960x540 — рисуем 1:1
            screen.blit(game_surface, (offset_x, offset_y))
        else:
            # целочисленный масштаб (2x, 3x, ...) — картинка остаётся чёткой
            scaled_surface = pygame.transform.scale(
                game_surface,
                (WIDTH * scale, HEIGHT * scale)
            )
            screen.blit(scaled_surface, (offset_x, offset_y))

        pygame.display.flip()
        clock.tick(60)

        if mode == "play" and not network_running:
            add_message("Соединение потеряно. Нажмите Esc для выхода.")

    network_running = False
    if network_socket is not None:
        try:
            network_socket.close()
        except Exception:
            pass
    pygame.quit()
    sys.exit()


if __name__ == "__main__":
    main()
