
# server.py
# Онлайновый 2D-рогалик "Башня Забытого Пламени" — сервер
import socket
import threading
import json
import time
import random
import sys
import traceback

# Размеры условной карты (в логике сервера — координаты, в клиенте визуализируются в тайлах)
MAP_WIDTH = 20
MAP_HEIGHT = 12

# Тайминги
TICK_INTERVAL = 0.03          # ещё более частые тики для максимальной плавности
DEATH_TIMEOUT = 300           # 5 минут до рестарта на 1 уровень
ENEMY_ATTACK_DELAY = 1.0      # враги атакуют не чаще, чем раз в N секунд
ENEMY_MOVE_INTERVAL = 0.03    # враги ближники двигаются не чаще чем в N секунд
RESPAWN_INTERVAL = 60.0       # каждые 60 секунд враги возрождаются на уровне (если не зачищен)
DOOR_RESPAWN_INTERVAL = 120.0     # каждые 2 минуты волна на уровне с дверью
HP_REGEN_DELAY = 10.0         # через сколько секунд без урона/атаки начать реген HP
MANA_REGEN_DELAY = 10.0       # через сколько секунд после траты маны начать реген MP
HP_REGEN_STEP = 2             # сколько HP в секунду восстанавливать
MANA_REGEN_STEP = 2           # сколько MP в секунду восстанавливать



# --- Изгнанник, босс 10 уровня ---

# Интервал между респавнами Изгнанника (только для 10 уровня)
BOSS_10_RESPAWN_INTERVAL = 1800.0  # 30 минут
# Время телеграфа перед появлением (фаза 0)
BOSS_10_SPAWN_TELEGRAPH = 10.0  # секунд
# Радиус круга появления в тайлах (диаметр ≈ 9 тайлов)
BOSS_10_SPAWN_RADIUS_TILES = 4.5
# Количество боевых фаз босса
BOSS_10_MAX_PHASE = 4
# Кулдаун способности «Пульс пламени» (фаза 4)
BOSS_10_PULSE_COOLDOWN = 10.0  # секунд
BOSS_10_RESPAWN_DAMAGE_FRACTION = 0.5 # Доля текущего HP, которую теряют игроки, стоящие в круге при респавне

# --- Фаза 2 Изгнанника (зелёные круги по полу) ---
BOSS_10_PHASE2_THRESHOLD = 0.75          # порог HP: с 1-й фазы в 2-ю
BOSS_10_PHASE2_DEF_BONUS = 2             # +броня при входе во 2-ю фазу

BOSS_10_PHASE2_MAX_CIRCLES = 10          # максимум одновременно активных кругов
BOSS_10_PHASE2_SPAWN_INTERVAL = 2.5      # раз в N секунд пытаемся создать новый круг

BOSS_10_PHASE2_RADIUS_TILES = 0.8        # радиус опасной зоны в тайлах
BOSS_10_PHASE2_TELEGRAPH_TIME = 3.0      # сколько секунд круг телеграфит (контур)
BOSS_10_PHASE2_ACTIVE_TIME = 1.0         # сколько секунд круг горит как «активный»

BOSS_10_PHASE2_DAMAGE = 20               # урон по игроку при срабатывании круга



def send_json(sock, obj):
    try:
        data = json.dumps(obj, ensure_ascii=False) + "\n"
        sock.sendall(data.encode("utf-8"))
    except Exception:
        pass


def recv_json_line(f):
    line = f.readline()
    if not line:
        return None
    line = line.strip()
    if not line:
        return None
    return json.loads(line)


class Player:
    def __init__(self, pid, name, cls_name, conn, fileobj):
        self.id = pid
        self.name = name
        self.cls = cls_name
        self.conn = conn
        self.file = fileobj

        self.stage = 0
        self.x = MAP_WIDTH / 2.0
        self.y = MAP_HEIGHT / 2.0

        self.max_hp = 0
        self.hp = 0
        self.max_mana = 0
        self.mana = 0
        self.attack = 0
        self.defense = 0
        self.special_cd = 0.0
        self.last_special_time = 0.0

        self.alive = True
        self.dead_since = None

        # для регена
        now = time.time()
        self.last_damage_time = now
        self.last_attack_time = now
        self.last_mana_spent_time = now
        self.last_hp_regen_time = now
        self.last_mana_regen_time = now

        # состояние длительных способностей (например, канал щита воина)
        self.special_active = False
        self.special_mode = None
        self.special_last_tick = now

        # Стойка лучника: "move" (Движение) или "ready" (Наизготовка)
        self.archer_stance = "move"

        self.can_attack = True  # хилер не может атаковать


class Enemy:
    def __init__(self, eid, name, etype, hp, attack, defense, x, y, miniboss=False, boss=False):
        self.id = eid
        self.name = name
        self.etype = etype  # 'melee' или 'ranged'
        self.max_hp = hp
        self.hp = hp
        self.attack = attack
        self.defense = defense
        self.x = float(x)
        self.y = float(y)
        self.miniboss = miniboss
        self.boss = boss


class LevelState:
    def __init__(self, stage, width, height):
        self.stage = stage
        self.width = width
        self.height = height

        self.enemies = []
        self.last_enemy_attack = time.time()
        self.last_enemy_move = time.time()
        self.shield_buff_until = 0.0
        self.completed = False
        self.last_respawn = time.time()

        # дверь на следующий уровень
        self.door_open = False
        self.door_x = None
        self.door_y = None



        # --- Состояние босса 10 уровня (Изгнанник) ---
        # Текущая фаза босса: None, 1..BOSS_10_MAX_PHASE
        self.boss_phase = None
        self.boss_max_phase = BOSS_10_MAX_PHASE

        # Жив ли сейчас босс на уровне
        self.boss_alive = False

        # Время последней смерти босса (для отсчёта 30 минут до следующего появления)
        self.boss_last_death_time = 0.0

        # Ожидается ли особый респавн босса (фаза 0 – круг на полу)
        self.boss_spawn_pending = False

        # Параметры круга появления:
        # dict: {"x": float, "y": float, "radius": float, "start_time": float}
        # или None, если круга нет.
        self.boss_spawn_circle = None

        # Кол-во «аддов» фазы 3, которые сейчас живы
        self.boss_adds_alive = 0

        # Кулдаун способности «Пульс пламени» (фаза 4)
        self.boss_last_pulse_time = 0.0

        # Таймер для генерации кругов фазы 2
        self.boss_phase2_last_circle_time = 0.0

        # Общий список «опасных зон» уровня (телеграфы кругов и т.п.)
        # Каждый элемент — dict, который позже будем описывать:
        # {"type": "circle", "x": float, "y": float, "radius": float,
        #  "start_time": float, "warn_time": float, "active_time": float}
        self.hazards = []

    def enemies_alive(self):
        return any(e.hp > 0 for e in self.enemies)


class GameServer:
    def __init__(self):
        self.players = {}   # pid -> Player
        self.levels = {}    # stage -> LevelState
        self.next_player_id = 1
        self.next_enemy_id = 1
        self.lock = threading.Lock()
        self.running = True

    # --------- Игровая логика ---------

    def create_player_stats(self, p: Player):
        cls = p.cls.lower()
        now = time.time()
        if cls in ("воин", "warrior"):
            p.max_hp = 160
            p.max_mana = 10
            p.attack = 20
            p.defense = 7
            p.special_cd = 30.0
            p.cls = "воин"
            p.can_attack = True
        elif cls in ("лучник", "archer"):
            p.max_hp = 120
            p.max_mana = 40
            p.attack = 22
            p.defense = 4
            p.special_cd = 10.0
            p.cls = "лучник"
            p.can_attack = True
        elif cls in ("маг", "mage"):
            p.max_hp = 10000 # 90 в базе, 10000 в тесте
            p.max_mana = 10000 # 70 в базе, 10000 в тесте
            p.attack = 16
            p.defense = 3
            p.special_cd = 0.0
            p.cls = "маг"
            p.can_attack = True
        elif cls in ("хилер", "хиллер", "healer"):
            p.max_hp = 110
            p.max_mana = 80
            p.attack = 0
            p.defense = 4
            p.special_cd = 2.0
            p.cls = "хилер"
            p.can_attack = False
        else:
            p.max_hp = 130
            p.max_mana = 35
            p.attack = 18
            p.defense = 5
            p.special_cd = 15.0
            p.cls = "воин"
            p.can_attack = True

        p.hp = p.max_hp
        p.mana = p.max_mana
        w, h = self.get_map_size_for_stage(p.stage)
        p.x = w / 2.0
        p.y = h / 2.0

        p.last_damage_time = now
        p.last_attack_time = now
        p.last_mana_spent_time = now
        p.last_hp_regen_time = now
        p.last_mana_regen_time = now

    
    def get_map_size_for_stage(self, stage: int):
        """Размер карты: до 10 уровня — 20x12, с 11 уровня — 40x24."""
        if stage >= 11:
            return MAP_WIDTH * 2, MAP_HEIGHT * 2
        else:
            return MAP_WIDTH, MAP_HEIGHT



    def get_level(self, stage: int) -> LevelState:
        lvl = self.levels.get(stage)
        if lvl is None:
            w, h = self.get_map_size_for_stage(stage)
            lvl = LevelState(stage, w, h)

            if stage == 0:
                # ХАБ: нет врагов, только дверь наверх
                lvl.enemies = []
                lvl.completed = True
                lvl.door_open = True
                lvl.door_x = w / 2.0
                lvl.door_y = 2.0
            elif stage == 11:
                # 11 уровень — "Безопасная зона"
                lvl.enemies = []
                lvl.completed = True
                lvl.door_open = True
                lvl.door_x = w / 2.0
                lvl.door_y = 2.0
            else:
                # обычные боевые уровни
                lvl.enemies = self.generate_enemies(stage)

            # ### Специальная первичная инициализация для 10 уровня (Изгнанник)
            if stage == 10:
                # если на уровне есть босс, помечаем, что он жив и находится в начальной фазе
                if any(e.boss for e in lvl.enemies):
                    lvl.boss_alive = True
                    lvl.boss_phase = 1
                    lvl.boss_last_death_time = 0.0
                else:
                    # подстраховка: если почему-то нет босса, считаем что он «мертв» с нулевого времени
                    lvl.boss_alive = False
                    lvl.boss_phase = None
                    lvl.boss_last_death_time = 0.0

            self.levels[stage] = lvl
        return lvl


    def generate_enemies(self, stage: int):
        enemies = []

        w, h = self.get_map_size_for_stage(stage)

        def rand_pos():
            return random.uniform(0, w - 1), random.uniform(0, h - 1)

        mob_pool = [
            ("Крыса тоннелей", "melee", 35, 8, 1),
            ("Культист забвения", "ranged", 45, 9, 2),
            ("Призрачный волк", "melee", 55, 11, 3),
            ("Осквернённый страж", "melee", 70, 13, 4),
            ("Тёмный стрелок", "ranged", 50, 12, 2),
        ]

        if stage == 10:
            x, y = rand_pos()
            enemies.append(self._make_enemy("Изгнанник", "melee", 500, 60, 4, x, y, boss=True))
        elif stage == 21:
            x, y = rand_pos()
            enemies.append(
                self._make_enemy(
                    "Владыка Забытого Пламени",
                    "ranged",
                    1000,
                    30,
                    8,
                    x, y,
                    boss=True
                )
            )
        elif stage % 2 == 0:
            # мини-боссы на чётных уровнях
            # после 10 уровня они заметно усиливаются
            if stage >= 11:
                base_hp = int((120 + stage * 12) * 1.8)
                base_atk = int((15 + stage) * 1.5)
                base_def = 4 + stage // 2 + 2
            else:
                base_hp = 120 + stage * 12
                base_atk = 15 + stage
                base_def = 4 + stage // 2

            name = f"Страж уровня {stage}"
            etype = "melee" if stage % 4 != 0 else "ranged"
            x, y = rand_pos()
            enemies.append(
                self._make_enemy(name, etype, base_hp, base_atk, base_def, x, y, miniboss=True)
            )

        else:
            # обычные волны мобов
            if stage >= 11:
                # после 10 уровня — больше мобов и выше характеристики
                count = 4 + stage     # было 2 + stage
                hp_scale = 10         # было *6
                atk_scale = 2.0       # было *1.6
            else:
                count = 2 + stage
                hp_scale = 6
                atk_scale = 1.6

            for _ in range(count):
                nm, etype, hp, atk, df = random.choice(mob_pool)
                hp = int(hp + stage * hp_scale)
                atk = int(atk + stage * atk_scale)
                df = int(df + stage // 2)
                x, y = rand_pos()
                enemies.append(self._make_enemy(nm, etype, hp, atk, df, x, y))

        return enemies

    def _make_enemy(self, name, etype, hp, atk, df, x, y, miniboss=False, boss=False):
        eid = self.next_enemy_id
        self.next_enemy_id += 1
        return Enemy(eid, name, etype, hp, atk, df, x, y, miniboss=miniboss, boss=boss)

    def calc_damage(self, attack, defense):
        base = attack - defense
        base += random.randint(-2, 2)
        if base < 1:
            base = 1
        return base

    def broadcast_event(self, msg, stage=None):
        print("[EVENT]", msg, flush=True)
        for p in list(self.players.values()):
            if stage is not None and p.stage != stage:
                continue
            send_json(p.conn, {"type": "event", "msg": msg})

    def broadcast_attack(self, stage, attacker_type, attacker_id, attacker_name,
                         from_x, from_y, target_type, target_id, target_name,
                         to_x, to_y, damage, special=False):
        payload = {
            "type": "attack",
            "stage": stage,
            "attacker_type": attacker_type,
            "attacker_id": attacker_id,
            "attacker_name": attacker_name,
            "from_x": from_x,
            "from_y": from_y,
            "target_type": target_type,
            "target_id": target_id,
            "target_name": target_name,
            "to_x": to_x,
            "to_y": to_y,
            "damage": damage,
            "special": special,
        }
        for p in list(self.players.values()):
            if p.stage == stage:
                send_json(p.conn, payload)


    def send_state(self, player: Player):
        lvl = self.get_level(player.stage)
        now = time.time()

        enemies_payload = [
            {
                "id": e.id,
                "name": e.name,
                "etype": e.etype,
                "hp": max(e.hp, 0),
                "max_hp": e.max_hp,
                "boss": e.boss,
                "miniboss": e.miniboss,
                "x": e.x,
                "y": e.y,
            }
            for e in lvl.enemies if e.hp > 0
        ]

        players_payload = []
        for p in self.players.values():
            if p.stage != player.stage:
                continue
            players_payload.append({
                "id": p.id,
                "name": p.name,
                "class": p.cls,
                "hp": p.hp,
                "max_hp": p.max_hp,
                "mana": p.mana,
                "max_mana": p.max_mana,
                "stage": p.stage,
                "alive": p.alive,
                "x": p.x,
                "y": p.y,
                "archer_stance": getattr(p, "archer_stance", "move"),
            })

        special_left = 0.0
        if player.special_cd > 0:
            special_left = max(0.0, player.special_cd - (now - player.last_special_time))

        # таймер респавна
        next_respawn_in = 0

        if lvl.stage == 10:
            # Для Изгнанника показываем, сколько осталось до особого респавна
            if not getattr(lvl, "boss_alive", False) and not getattr(lvl, "boss_spawn_pending", False):
                death_time = getattr(lvl, "boss_last_death_time", 0.0) or 0.0
                if death_time > 0.0:
                    passed = now - death_time
                    if passed < BOSS_10_RESPAWN_INTERVAL:
                        next_respawn_in = max(0, int(BOSS_10_RESPAWN_INTERVAL - passed))
        elif lvl.stage != 0 and lvl.stage != 11:
            # Обычная логика для остальных уровней
            if lvl.door_x is None:
                if lvl.enemies_alive():
                    next_respawn_in = max(0, int(RESPAWN_INTERVAL - (now - lvl.last_respawn)))
            else:
                if not lvl.enemies_alive():
                    next_respawn_in = max(0, int(DOOR_RESPAWN_INTERVAL - (now - lvl.last_respawn)))

        door_info = {
            "open": lvl.door_open,
            "x": lvl.door_x,
            "y": lvl.door_y,
        }

        payload = {
            "type": "state",
            "you": {
                "id": player.id,
                "name": player.name,
                "class": player.cls,
                "hp": player.hp,
                "max_hp": player.max_hp,
                "mana": player.mana,
                "max_mana": player.max_mana,
                "stage": player.stage,
                "alive": player.alive,
                "x": player.x,
                "y": player.y,
                "archer_stance": getattr(player, "archer_stance", "move"),
                "special_cd": player.special_cd,
                "special_cd_left": special_left,
            },
            "level": {
                "stage": player.stage,
                "width": lvl.width,
                "height": lvl.height,
                "shield_active": time.time() < lvl.shield_buff_until,
                "enemies": enemies_payload,
                "next_respawn_in": next_respawn_in,
                "door": door_info,

                # --- Доп. информация для логики босса и эффектов уровня ---
                # Список опасных зон (пока всегда пуст, заполним на следующих этапах)
                "hazards": getattr(lvl, "hazards", []),

                # Фаза босса 10 уровня (None, если босса нет или другой уровень)
                "boss_phase": getattr(lvl, "boss_phase", None),

                # Параметры круга появления босса (фаза 0) или None
                "boss_spawn_circle": getattr(lvl, "boss_spawn_circle", None),
            },
            "players": players_payload,
        }
        send_json(player.conn, payload)


    def broadcast_state_for_level(self, stage: int):
        for p in self.players.values():
            if p.stage == stage:
                self.send_state(p)


    def check_and_open_door(self, stage: int):
        lvl = self.get_level(stage)
        # ХАБ не использует механику зачистки/двери
        if lvl.stage == 0:
            return
        if lvl.door_open:
            # дверь уже открыта
            return
        if not lvl.enemies_alive():
            now = time.time()
            lvl.completed = True
            # если двери ещё не было — создаём; иначе просто открываем существующую
            if lvl.door_x is None or lvl.door_y is None:
                lvl.door_x = random.uniform(2, lvl.width - 2)
                lvl.door_y = random.uniform(2, lvl.height - 2)
            lvl.door_open = True
            # от двери отсчитываем таймер до следующего возможного респавна
            lvl.last_respawn = now
            self.broadcast_event(f"На уровне {stage} открылась дверь наверх!", stage=stage)

    def enemies_move_level(self, stage: int):
        """Плавное движение ближников к ближайшему живому игроку."""
        lvl = self.get_level(stage)
        alive_enemies = [e for e in lvl.enemies if e.hp > 0]
        if not alive_enemies:
            return

        alive_players = [p for p in self.players.values()
                         if p.stage == stage and p.alive]
        if not alive_players:
            return

        for enemy in alive_enemies:
            # двигаем только ближников, дальники стоят
            if enemy.etype != "melee":
                continue

            # ближайшая цель
            target = min(
                alive_players,
                key=lambda p: (p.x - enemy.x) ** 2 + (p.y - enemy.y) ** 2
            )
            dx = target.x - enemy.x
            dy = target.y - enemy.y
            dist2 = dx * dx + dy * dy

            # уже практически вплотную — не подходим, чтобы не залезать в игрока
            if dist2 <= 0.25 ** 2:
                continue

            length = (dist2) ** 0.5 or 1.0
            step = 0.1  # скорость ближника за один шаг движения
            move = min(step, length)

            enemy.x += dx / length * move
            enemy.y += dy / length * move

            # не выходим за границы карты
            enemy.x = max(0.0, min(lvl.width - 1, enemy.x))
            enemy.y = max(0.0, min(lvl.height - 1, enemy.y))



    def enemies_attack_level(self, stage: int):
        lvl = self.get_level(stage)
        alive_enemies = [e for e in lvl.enemies if e.hp > 0]
        if not alive_enemies:
            return
        alive_players = [p for p in self.players.values() if p.stage == stage and p.alive]
        if not alive_players:
            return

        now = time.time()
        lvl.last_enemy_attack = now

        for enemy in alive_enemies:
            alive_players = [p for p in self.players.values() if p.stage == stage and p.alive]
            if not alive_players:
                break

            # Особая логика для финального босса 21 уровня: дальник, бьёт сразу двух игроков
            if stage == 21 and enemy.boss and enemy.etype == "ranged":
                # сортируем игроков по расстоянию и берём двух ближайших
                sorted_players = sorted(
                    alive_players,
                    key=lambda p: (p.x - enemy.x) ** 2 + (p.y - enemy.y) ** 2
                )
                targets = sorted_players[:2]

                for target in targets:
                    dist2 = (target.x - enemy.x) ** 2 + (target.y - enemy.y) ** 2
                    # дальник может стрелять с любой дистанции, ограничений по расстоянию не ставим
                    dmg = self.calc_damage(enemy.attack, target.defense)
                    if now < lvl.shield_buff_until:
                        dmg = int(dmg * 0.6)
                        if dmg < 1:
                            dmg = 1
                    # учёт стойки лучника "Наизготовка" (получает x3)
                    t_cls = (target.cls or "").lower()
                    if t_cls == "лучник" and getattr(target, "archer_stance", "move") == "ready":
                        dmg = int(dmg * 3)
                        if dmg < 1:
                            dmg = 1

                    target.hp -= dmg
                    target.last_damage_time = now
                    if target.hp <= 0:
                        target.hp = 0
                        target.alive = False
                        target.dead_since = now
                        self.broadcast_event(f"{target.name} погиб от удара финального босса.", stage=stage)

                    self.broadcast_attack(
                        stage,
                        attacker_type="enemy",
                        attacker_id=enemy.id,
                        attacker_name=enemy.name,
                        from_x=enemy.x,
                        from_y=enemy.y,
                        target_type="player",
                        target_id=target.id,
                        target_name=target.name,
                        to_x=target.x,
                        to_y=target.y,
                        damage=dmg,
                        special=True,  # можно считать это "особой" атакой
                    )

                # после удара по двум целям переходим к следующему врагу
                continue

            # Обычная логика для всех остальных врагов
            target = min(
                alive_players,
                key=lambda p: (p.x - enemy.x) ** 2 + (p.y - enemy.y) ** 2
            )
            dist2 = (target.x - enemy.x) ** 2 + (target.y - enemy.y) ** 2

            if enemy.etype == "melee":
                # если далеко — подходим
                if dist2 > 1.5 ** 2:
                    dx = target.x - enemy.x
                    dy = target.y - enemy.y
                    length = (dx * dx + dy * dy) ** 0.5 or 1.0
                    step = 0.2
                    enemy.x += dx / length * min(step, length)
                    enemy.y += dy / length * min(step, length)
                    enemy.x = max(0.0, min(lvl.width - 1, enemy.x))
                    enemy.y = max(0.0, min(lvl.height - 1, enemy.y))

                    continue  # в этот тик не атакуем
                # ближний удар
            else:
                # дальний удар — можно стрелять из любой дистанции
                pass

            dmg = self.calc_damage(enemy.attack, target.defense)
            # Ближние враги наносят в 3 раза больше урона
            if enemy.etype == "melee":
                dmg = int(dmg * 3)
                if dmg < 1:
                    dmg = 1
            if now < lvl.shield_buff_until:
                dmg = int(dmg * 0.6)
                if dmg < 1:
                    dmg = 1
            # Лучник в стойке "Наизготовка" получает на 200% больше урона (x3)
            t_cls = (target.cls or "").lower()
            if t_cls == "лучник" and getattr(target, "archer_stance", "move") == "ready":
                dmg = int(dmg * 3)
                if dmg < 1:
                    dmg = 1
            target.hp -= dmg
            target.last_damage_time = now

            self.broadcast_event(
                f"{enemy.name} атакует {target.name} на {dmg} урона. ({max(target.hp,0)} HP)",
                stage=stage,
            )
            self.broadcast_attack(
                stage,
                attacker_type="enemy",
                attacker_id=enemy.id,
                attacker_name=enemy.name,
                from_x=enemy.x,
                from_y=enemy.y,
                target_type="player",
                target_id=target.id,
                target_name=target.name,
                to_x=target.x,
                to_y=target.y,
                damage=dmg,
                special=False,
            )
            if target.hp <= 0 and target.alive:
                target.alive = False
                target.dead_since = now
                self.broadcast_event(f"{target.name} пал на уровне {stage}!", stage=stage)

        self.check_and_open_door(stage)

    def move_player(self, player: Player, dx: float, dy: float):
        if not player.alive:
            return
        # Лучник в стойке "Наизготовка" не может двигаться
        cls = (player.cls or "").lower()
        if cls == "лучник" and getattr(player, "archer_stance", "move") == "ready":
            return
        # свободное перемещение — маленький шаг, клиент шлёт их часто
        lvl = self.get_level(player.stage)
        nx = player.x + float(dx)
        ny = player.y + float(dy)
        nx = max(0.0, min(lvl.width - 1, nx))
        ny = max(0.0, min(lvl.height - 1, ny))
        player.x = nx
        player.y = ny

    def update_boss10_phase_on_damage(self, lvl: LevelState, enemy: Enemy):
        """Обновляет фазу Изгнанника при снижении HP."""
        if lvl.stage != 10 or not enemy.boss or enemy.hp <= 0:
            return

        # Если фаза не инициализирована — считаем, что босс в 1-й фазе
        if lvl.boss_phase is None:
            lvl.boss_phase = 1

        # Переход 1 -> 2 при падении HP до 75%
        if lvl.boss_phase == 1 and enemy.hp <= enemy.max_hp * BOSS_10_PHASE2_THRESHOLD:
            lvl.boss_phase = 2
            enemy.defense += BOSS_10_PHASE2_DEF_BONUS
            self.broadcast_event(
                "Изгнанник покрывается коркой пепла — его броня крепнет, "
                "а по полу вспыхивают зелёные круги.",
                stage=lvl.stage,
            )

    def basic_attack(self, player: Player, target_enemy_id=None, target_player_id=None):
        if not player.alive:
            return

        now = time.time()
        cls = (player.cls or "").lower()

        # Хилер: вместо атаки — небольшой хил по SPACE
        if cls in ("хилер", "хиллер", "healer"):
            if player.mana < 1:
                send_json(player.conn, {"type": "error", "msg": "Недостаточно маны для исцеления (нужна 1 MP)."})
                return

            # цель хилла
            target = None
            if target_player_id is not None:
                try:
                    tid = int(target_player_id)
                    target = self.players.get(tid)
                    if target and target.stage != player.stage:
                        target = None
                except Exception:
                    target = None
            if target is None:
                target = player

            if not target.alive:
                send_json(player.conn, {"type": "error", "msg": "Цель мертва. Сначала воскресите её."})
                return

            old_hp = target.hp
            heal = 5
            target.hp = min(target.max_hp, target.hp + heal)
            actual = target.hp - old_hp
            if actual <= 0:
                send_json(player.conn, {"type": "event", "msg": f"{target.name} уже полностью здоров."})
                return

            player.mana -= 1
            player.last_mana_spent_time = now
            player.last_attack_time = now

            self.broadcast_event(
                f"{player.name} исцеляет {target.name} на {actual} HP (быстрый хил).",
                stage=player.stage,
            )
            self.broadcast_attack(
                player.stage,
                attacker_type="player",
                attacker_id=player.id,
                attacker_name=player.name,
                from_x=player.x,
                from_y=player.y,
                target_type="player",
                target_id=target.id,
                target_name=target.name,
                to_x=target.x,
                to_y=target.y,
                damage=-actual,
                special=False,
            )
            return

        # Для остальных проверяем, может ли класс вообще атаковать
        if not player.can_attack:
            send_json(player.conn, {"type": "error", "msg": "Ваш класс не может использовать обычную атаку."})
            return

        lvl = self.get_level(player.stage)
        alive_enemies = [e for e in lvl.enemies if e.hp > 0]
        if not alive_enemies:
            self.broadcast_event("На уровне больше нет врагов.", stage=player.stage)
            return

        # выбор цели
        target = None
        if target_enemy_id is not None:
            for e in alive_enemies:
                if e.id == target_enemy_id:
                    target = e
                    break
        if target is None:
            target = min(
                alive_enemies,
                key=lambda e: (e.x - player.x) ** 2 + (e.y - player.y) ** 2
            )

        # Воин: ближний бой — бить можно только рядом
        if cls == "воин":
            dist2 = (target.x - player.x) ** 2 + (target.y - player.y) ** 2
            if dist2 > 1.5 ** 2:
                send_json(player.conn, {"type": "error", "msg": "Цель слишком далеко для удара в ближнем бою."})
                return

        # Лучник: кд 1 сек на обычную атаку в стойке "Движение"
        if cls == "лучник":
            if getattr(player, "archer_stance", "move") != "ready":
                if now - player.last_attack_time < 1.0:
                    remain = 1.0 - (now - player.last_attack_time)
                    send_json(player.conn, {"type": "error", "msg": f"Выстрел ещё в откате ({remain:.1f} с)."})
                    return

        # Маг: обычная атака тратит 1 MP
        if cls == "маг":
            if player.mana < 1:
                send_json(player.conn, {"type": "error", "msg": "Недостаточно маны для атаки (нужна 1 MP)."})
                return
            player.mana -= 1
            player.last_mana_spent_time = now

        dmg = self.calc_damage(player.attack, target.defense)
        target.hp -= dmg
        player.last_attack_time = now

        self.broadcast_event(
            f"{player.name} атакует {target.name} на {dmg} урона. ({max(target.hp,0)} HP)",
            stage=player.stage,
        )
        self.broadcast_attack(
            player.stage,
            attacker_type="player",
            attacker_id=player.id,
            attacker_name=player.name,
            from_x=player.x,
            from_y=player.y,
            target_type="enemy",
            target_id=target.id,
            target_name=target.name,
            to_x=target.x,
            to_y=target.y,
            damage=dmg,
            special=False,
        )
        if target.hp <= 0:
            # Особая обработка смерти Изгнанника на 10 уровне
            if player.stage == 10 and target.boss:
                lvl.boss_alive = False
                lvl.boss_phase = None
                lvl.boss_last_death_time = now
                lvl.boss_spawn_pending = False
                lvl.boss_spawn_circle = None
                # убираем круг появления из списка опасностей, если он вдруг остался
                lvl.hazards = [h for h in lvl.hazards if h.get("type") != "boss10_spawn"]

            self.broadcast_event(f"{target.name} повержен!", stage=player.stage)
            self.check_and_open_door(player.stage)



    def use_special(self, player: Player, target_player_id=None):
        now = time.time()
        cls = (player.cls or "").lower()

        # общий кд — не действует на мага (у мага нет кд на спец)
        if cls != "маг" and player.special_cd > 0 and now - player.last_special_time < player.special_cd:
            remain = int(player.special_cd - (now - player.last_special_time))
            send_json(player.conn, {"type": "error", "msg": f"Способность в откате, ещё {remain} с."})
            return

        lvl = self.get_level(player.stage)
        alive_enemies = [e for e in lvl.enemies if e.hp > 0]

        if cls == "воин":
            # щит, который действует пока есть мана (каждую секунду -1 MP, всего 10 MP)
            if player.mana <= 0:
                send_json(player.conn, {"type": "error", "msg": "Недостаточно маны для Боевого клича."})
                return
            player.special_active = True
            player.special_mode = "warrior_shield"
            player.special_last_tick = now
            player.last_mana_spent_time = now
            lvl.shield_buff_until = now + 1.5  # поддерживаем небольшой запас, тик будет продлевать
            self.broadcast_event(
                f"{player.name} использует 'Боевой клич': щит действует, пока у него есть мана!",
                stage=player.stage,
            )

        elif cls == "лучник":
            # Переключение стойки лучника: "Движение" <-> "Наизготовка"
            current = getattr(player, "archer_stance", "move")
            if current == "ready":
                player.archer_stance = "move"
                stance_name = "Движение"
            else:
                player.archer_stance = "ready"
                stance_name = "Наизготовка"
            self.broadcast_event(
                f"{player.name} переключает стойку: теперь '{stance_name}'.",
                stage=player.stage,
            )

        elif cls == "маг":
            cost = 15
            if player.mana < cost:
                send_json(player.conn, {"type": "error", "msg": "Недостаточно маны."})
                return
            if not alive_enemies:
                send_json(player.conn, {"type": "error", "msg": "На уровне нет врагов."})
                return
            player.mana -= cost
            player.last_mana_spent_time = now
            total = 0
            for enemy in alive_enemies:
                dmg = self.calc_damage(player.attack + 5, enemy.defense)
                enemy.hp -= dmg
                total += dmg
                self.broadcast_attack(
                    player.stage,
                    attacker_type="player",
                    attacker_id=player.id,
                    attacker_name=player.name,
                    from_x=player.x,
                    from_y=player.y,
                    target_type="enemy",
                    target_id=enemy.id,
                    target_name=enemy.name,
                    to_x=enemy.x,
                    to_y=enemy.y,
                    damage=dmg,
                    special=True,
                )
            player.last_attack_time = now
            self.broadcast_event(
                f"{player.name} кидает 'Огненный шар', нанося {total} суммарного урона всем врагам!",
                stage=player.stage,
            )
            for enemy in alive_enemies:
                if enemy.hp <= 0:

                    # Особая обработка смерти Изгнанника на 10 уровне
                    if player.stage == 10 and enemy.boss:
                        lvl = self.get_level(player.stage)
                        lvl.boss_alive = False
                        lvl.boss_phase = None
                        lvl.boss_last_death_time = now
                        lvl.boss_spawn_pending = False
                        lvl.boss_spawn_circle = None
                        lvl.hazards = [h for h in lvl.hazards if h.get("type") != "boss10_spawn"]

                    self.broadcast_event(f"{enemy.name} сгорел дотла!", stage=player.stage)
            self.check_and_open_door(player.stage)

        elif cls in ("хилер", "хиллер", "healer"):
            cost = 10
            if player.mana < cost:
                send_json(player.conn, {"type": "error", "msg": "Недостаточно маны для исцеления."})
                return
            # выбираем основную цель
            target = None
            if target_player_id is not None:
                try:
                    tid = int(target_player_id)
                    target = self.players.get(tid)
                    if target and target.stage != player.stage:
                        target = None
                except Exception:
                    target = None
            if target is None:
                target = player
            if not target.alive:
                send_json(player.conn, {"type": "error", "msg": "Цель мертва. Сначала воскресите её."})
                return

            # основная цель — мощный хил, остальные живые союзники на уровне — по 10 HP
            allies = [p for p in self.players.values() if p.stage == player.stage and p.alive]

            # большой хил основной цели
            old_hp_main = target.hp
            heal_main = max(10, int(target.max_hp * 0.3))
            target.hp = min(target.max_hp, target.hp + heal_main)
            actual_main = target.hp - old_hp_main

            if actual_main <= 0 and all(a.hp >= a.max_hp for a in allies):
                send_json(player.conn, {"type": "event", "msg": f"{target.name} уже полностью здоров."})
                return

            player.mana -= cost
            player.last_mana_spent_time = now

            # лечим остальных союзников на 10 HP
            for ally in allies:
                if ally.id == target.id:
                    continue
                if ally.hp >= ally.max_hp:
                    continue
                heal_small = min(10, ally.max_hp - ally.hp)
                if heal_small <= 0:
                    continue
                ally.hp += heal_small
                self.broadcast_attack(
                    player.stage,
                    attacker_type="player",
                    attacker_id=player.id,
                    attacker_name=player.name,
                    from_x=player.x,
                    from_y=player.y,
                    target_type="player",
                    target_id=ally.id,
                    target_name=ally.name,
                    to_x=ally.x,
                    to_y=ally.y,
                    damage=-heal_small,
                    special=True,
                )

            # событие и визуализация основной цели
            self.broadcast_event(
                f"{player.name} мощно исцеляет {target.name} и лечит союзников вокруг!",
                stage=player.stage,
            )
            if actual_main > 0:
                self.broadcast_attack(
                    player.stage,
                    attacker_type="player",
                    attacker_id=player.id,
                    attacker_name=player.name,
                    from_x=player.x,
                    from_y=player.y,
                    target_type="player",
                    target_id=target.id,
                    target_name=target.name,
                    to_x=target.x,
                    to_y=target.y,
                    damage=-actual_main,
                    special=True,
                )

        else:
            send_json(player.conn, {"type": "error", "msg": "У вашего класса нет особой способности."})
            return

        player.last_special_time = now

    def resurrect_player(self, caster: Player, target_player_id=None, target_name=None):
        target = None
        target_name = (target_name or "").strip()
        if target_player_id is not None:
            try:
                target = self.players.get(int(target_player_id))
            except Exception:
                target = None
        elif target_name:
            for p in self.players.values():
                if p.name.lower() == target_name.lower() or str(p.id) == target_name:
                    target = p
                    break

        if target is None:
            send_json(caster.conn, {"type": "error", "msg": "Игрок для воскрешения не найден."})
            return

        cost = 15
        now = time.time()
        if caster.mana < cost:
            send_json(caster.conn, {"type": "error", "msg": "Недостаточно маны для воскрешения."})
            return

        if target.alive:
            send_json(caster.conn, {"type": "error", "msg": "Этот игрок уже жив."})
            return
        if target.dead_since is None:
            send_json(caster.conn, {"type": "error", "msg": "Этого игрока нельзя воскресить."})
            return
        if now - target.dead_since > DEATH_TIMEOUT:
            send_json(caster.conn, {"type": "error", "msg": "Прошло слишком много времени, рестарт уже произошёл."})
            return

        caster.mana -= cost
        caster.last_mana_spent_time = now
        target.alive = True
        target.dead_since = None
        target.stage = caster.stage
        target.x = caster.x
        target.y = caster.y
        target.hp = max(1, int(target.max_hp * 0.5))
        if (target.cls or "").lower() == "лучник":
            target.archer_stance = "move"
        self.broadcast_event(
            f"{caster.name} воскрешает {target.name} на уровне {caster.stage}!",
            stage=caster.stage,
        )

    def respawn_to_start(self, player: Player):
        now = time.time()
        player.stage = 0
        player.alive = True
        player.dead_since = None
        player.hp = player.max_hp
        player.mana = player.max_mana
        w, h = self.get_map_size_for_stage(0)
        player.x = w / 2.0
        player.y = h / 2.0

        player.last_damage_time = now
        player.last_attack_time = now
        player.last_mana_spent_time = now
        player.last_hp_regen_time = now
        player.last_mana_regen_time = now
        # При полном респауне лучник возвращается в стойку движения
        if (player.cls or "").lower() == "лучник":
            player.archer_stance = "move"
        self.broadcast_event(
            f"{player.name} слишком долго был мёртв и возвращается в ХАБ.",
            stage=0,
        )

    def try_enter_door(self, player: Player):
        lvl = self.get_level(player.stage)
        if not lvl.door_open or lvl.door_x is None:
            send_json(player.conn, {"type": "error", "msg": "Дверь ещё не открыта."})
            return
        dx = player.x - lvl.door_x
        dy = player.y - lvl.door_y
        if dx * dx + dy * dy > 0.6 * 0.6:
            send_json(player.conn, {"type": "error", "msg": "Подойдите вплотную к двери, чтобы войти."})
            return

        stage = player.stage
        if stage >= 21:
            self.broadcast_event(f"{player.name} достигает вершины Башни. Победа!", stage=stage)
            return

        new_stage = stage + 1
        w, h = self.get_map_size_for_stage(new_stage)
        player.stage = new_stage
        player.x = w / 2.0
        player.y = h / 2.0
        heal_hp = int(player.max_hp * 0.3)
        heal_mana = int(player.max_mana * 0.3)
        player.hp = min(player.max_hp, player.hp + heal_hp)
        player.mana = min(player.max_mana, player.mana + heal_mana)
        self.broadcast_event(f"{player.name} поднимается на уровень {new_stage}.", stage=new_stage)
        self.get_level(new_stage)
        self.send_state(player)
        self.broadcast_state_for_level(new_stage)


    def handle_command(self, player: Player, msg: dict):
        cmd = (msg.get("command") or "").lower()
        if not cmd:
            return

        if not player.alive and cmd not in ("status", "who", "help"):
            send_json(player.conn, {"type": "error", "msg": "Вы мертвы. Ждите воскрешения или рестарта."})
            return

        dirty = False

        if cmd == "move":
            dx = float(msg.get("dx", 0.0))
            dy = float(msg.get("dy", 0.0))
            self.move_player(player, dx, dy)
            dirty = True

        elif cmd == "attack":
            target_enemy_id = msg.get("target_enemy_id")
            if target_enemy_id is not None:
                try:
                    target_enemy_id = int(target_enemy_id)
                except Exception:
                    target_enemy_id = None
            target_player_id = msg.get("target_player_id")
            if target_player_id is not None:
                try:
                    target_player_id = int(target_player_id)
                except Exception:
                    target_player_id = None
            self.basic_attack(player, target_enemy_id=target_enemy_id, target_player_id=target_player_id)
            dirty = True

        elif cmd == "special":
            target_player_id = msg.get("target_player_id")
            self.use_special(player, target_player_id=target_player_id)
            dirty = True

        elif cmd == "res":
            target_id = msg.get("target_player_id")
            target_name = msg.get("target")
            self.resurrect_player(player, target_player_id=target_id, target_name=target_name)
            dirty = True

        elif cmd == "enter_door":
            self.try_enter_door(player)
            dirty = True

        elif cmd == "status":
            self.send_state(player)

        elif cmd == "who":
            names = ", ".join(
                f"{p.id}:{p.name}({p.cls}){'†' if not p.alive else ''}"
                for p in self.players.values()
            )
            send_json(player.conn, {"type": "event", "msg": "Игроки: " + names})

        elif cmd == "help":
            txt = (
                "Управление: движение WASD/стрелки (удерживать), удар/хил SPACE, спец Q, воскрешение R.\n"
                "Выбор цели — ЛКМ по врагу/союзнику, переход на следующий уровень — через дверь."
            )
            send_json(player.conn, {"type": "event", "msg": txt})

        else:
            send_json(player.conn, {"type": "error", "msg": "Неизвестная команда."})

        if dirty:
            # после каждого важного действия сразу шлём состояние уровня, чтобы всё было максимально плавно
            self.broadcast_state_for_level(player.stage)

    # --------- Сетевое взаимодействие ---------

    def client_thread(self, player: Player):
        f = player.file
        conn = player.conn
        try:
            send_json(conn, {
                "type": "welcome",
                "msg": f"Добро пожаловать, {player.name}! Вы {player.cls}. Вы начинаете в ХАБе (уровень 0).",
                "player_id": player.id
            })
            self.send_state(player)
            self.broadcast_event(f"{player.name} подключился как {player.cls}.", stage=player.stage)

            while self.running:
                msg = recv_json_line(f)
                if msg is None:
                    break
                if msg.get("type") == "command":
                    with self.lock:
                        self.handle_command(player, msg)
        except Exception:
            traceback.print_exc()
        finally:
            with self.lock:
                if player.id in self.players:
                    del self.players[player.id]
            try:
                conn.close()
            except Exception:
                pass
            self.broadcast_event(f"{player.name} отключился от сервера.", stage=player.stage)

    def spawn_boss10_with_circle_damage(self, lvl: LevelState, now: float):
        """Появление Изгнанника в центре круга и урон игрокам внутри круга."""
        stage = lvl.stage
        circle = lvl.boss_spawn_circle or {}
        cx = float(circle.get("x", lvl.width / 2.0))
        cy = float(circle.get("y", lvl.height / 2.0))
        radius = float(circle.get("radius", BOSS_10_SPAWN_RADIUS_TILES))

        radius2 = radius * radius

        # Урон игрокам, стоящим в круге: 50% текущего HP, минимум 1
        for p in self.players.values():
            if p.stage != stage or not p.alive:
                continue
            dx = p.x - cx
            dy = p.y - cy
            if dx * dx + dy * dy <= radius2:
                dmg = max(1, int(p.hp * BOSS_10_RESPAWN_DAMAGE_FRACTION))
                p.hp -= dmg
                if p.hp <= 0:
                    p.hp = 0
                    p.alive = False
                    p.dead_since = now
                    self.broadcast_event(
                        f"{p.name} был сожжён зелёным пламенем при возвращении Изгнанника.",
                        stage=stage,
                    )
                p.last_damage_time = now

        # Спавним самого Изгнанника в центре круга
        enemy = self._make_enemy("Изгнанник", "melee", 500, 60, 4, cx, cy, boss=True)
        lvl.enemies.append(enemy)
        lvl.boss_alive = True
        lvl.boss_phase = 1
        lvl.boss_spawn_pending = False
        lvl.boss_spawn_circle = None

        # удаляем круг появления из hazards
        lvl.hazards = [h for h in lvl.hazards if h.get("type") != "boss10_spawn"]

        self.broadcast_event("Изгнанник восстаёт из зелёного пламени!", stage=stage)

    def update_boss10_respawn(self, lvl: LevelState, now: float):
        """
        Особая логика респавна Изгнанника на 10 уровне:
        - если босс жив — ничего не делаем;
        - после смерти ждём 30 минут;
        - затем показываем зелёный круг (фаза 0) на 10 секунд;
        - после чего босс появляется в центре круга.
        """
        stage = lvl.stage

        # 1) Проверяем, жив ли сейчас босс по факту
        boss_alive_now = any(e.hp > 0 and e.boss for e in lvl.enemies)
        if boss_alive_now:
            lvl.boss_alive = True
            lvl.boss_spawn_pending = False
            lvl.boss_spawn_circle = None
            # на всякий случай чистим круг появления
            lvl.hazards = [h for h in lvl.hazards if h.get("type") != "boss10_spawn"]
            return

        # Босс считаем мёртвым
        lvl.boss_alive = False

        # 2) Если уже идёт телеграф круга появления — ждём окончания 10 секунд
        circle = lvl.boss_spawn_circle
        if lvl.boss_spawn_pending and circle:
            start_time = circle.get("start_time", now)
            elapsed = now - start_time
            if elapsed >= BOSS_10_SPAWN_TELEGRAPH:
                # время спавнить босса
                self.spawn_boss10_with_circle_damage(lvl, now)
            return

        # 3) Если босс ещё ни разу не умирал — нечего респавнить
        if lvl.boss_last_death_time <= 0.0:
            return

        # 4) Ждём 30 минут с момента последней смерти
        elapsed_since_death = now - lvl.boss_last_death_time
        if elapsed_since_death < BOSS_10_RESPAWN_INTERVAL:
            return

        # 5) Запускаем телеграф круга появления в центре карты
        cx = lvl.width / 2.0
        cy = lvl.height / 2.0

        circle = {
            "type": "boss10_spawn",
            "x": cx,
            "y": cy,
            "radius": BOSS_10_SPAWN_RADIUS_TILES,
            "start_time": now,
        }
        lvl.boss_spawn_pending = True
        lvl.boss_spawn_circle = circle

        # Чистим старые круги этого типа и добавляем новый
        lvl.hazards = [h for h in lvl.hazards if h.get("type") != "boss10_spawn"]
        lvl.hazards.append(circle)

        self.broadcast_event(
            "Под ногами вспыхивает зелёное пламя — Изгнанник готовится вернуться...",
            stage=stage,
        )



    def tick_loop(self):
        while self.running:
            try:
                time.sleep(TICK_INTERVAL)
                with self.lock:
                    now = time.time()
                    # проверяем мёртвых на рестарт + реген
                    for p in list(self.players.values()):
                        if not p.alive and p.dead_since is not None:
                            if now - p.dead_since >= DEATH_TIMEOUT:
                                self.respawn_to_start(p)
                                self.send_state(p)

                        if p.alive:
                            # реген маны
                            if now - p.last_mana_spent_time >= MANA_REGEN_DELAY:
                                if now - p.last_mana_regen_time >= 1.0 and p.mana < p.max_mana:
                                    p.mana += MANA_REGEN_STEP
                                    if p.mana > p.max_mana:
                                        p.mana = p.max_mana
                                    p.last_mana_regen_time = now
                            # реген HP
                            idle_time = now - max(p.last_damage_time, p.last_attack_time)
                            if idle_time >= HP_REGEN_DELAY:
                                if now - p.last_hp_regen_time >= 1.0 and p.hp < p.max_hp:
                                    p.hp += HP_REGEN_STEP
                                    if p.hp > p.max_hp:
                                        p.hp = p.max_hp
                                    p.last_hp_regen_time = now

                            # канал длительных способностей (щит воина по мане)
                            if (p.cls or "").lower() == "воин" and getattr(p, "special_active", False):
                                lvl_p = self.get_level(p.stage)
                                if now - p.special_last_tick >= 1.0:
                                    if p.mana > 0:
                                        p.mana -= 1
                                        if p.mana < 0:
                                            p.mana = 0
                                        p.last_mana_spent_time = now
                                        p.special_last_tick = now
                                        # продлеваем щит ещё немного, пока идёт канал
                                        lvl_p.shield_buff_until = now + 1.5
                                    else:
                                        p.special_active = False
                                        p.special_mode = None
                                        self.broadcast_event(
                                            f"Щит {p.name} исчез — мана исчерпана.",
                                            stage=p.stage,
                                        )

                    # движение, автоатака врагов и респавн
                    for stage, lvl in self.levels.items():
                        # ХАБ пропускаем
                        if stage == 0 or stage == 11:
                            continue

                        # есть ли живые игроки на уровне
                        has_players = any(
                            p.stage == stage and p.alive
                            for p in self.players.values()
                        )

                        # --- движение ближников ---
                        if lvl.enemies_alive() and has_players:
                            if now - lvl.last_enemy_move >= ENEMY_MOVE_INTERVAL:
                                self.enemies_move_level(stage)
                                lvl.last_enemy_move = now

                        # --- атака врагов ---
                        if lvl.enemies_alive() and has_players and \
                                now - lvl.last_enemy_attack >= ENEMY_ATTACK_DELAY:
                            self.enemies_attack_level(stage)

                        # если игроков нет — дальше ничего не делаем для уровня
                        if not has_players:
                            continue

                        # --- логика респавна волн / двери (оставляем как было) ---

                        if stage == 10:
                            self.update_boss10_respawn(lvl, now)
                        else:
                            # Обычная логика волн и двери
                            if lvl.door_x is None:
                                # волны до появления двери
                                if lvl.enemies_alive():
                                    if now - lvl.last_respawn >= RESPWAN_INTERVAL:
                                        lvl.enemies = self.generate_enemies(stage)
                                        lvl.last_respawn = now
                                        self.broadcast_event(
                                            f"На уровне {stage} появились новые враги!",
                                            stage=stage,
                                        )
                                else:
                                    # если все враги умерли до появления двери — можно открыть дверь
                                    self.check_and_open_door(stage)
                            else:
                                # после того как дверь появилась, волны идут раз в 2 минуты,
                                # если уровень не зачищен
                                if not lvl.enemies_alive():
                                    if now - lvl.last_respawn >= DOOR_RESPAWN_INTERVAL and not lvl.completed:
                                        lvl.enemies = self.generate_enemies(stage)
                                        lvl.last_respawn = now
                                        lvl.door_open = False
                                        self.broadcast_event(
                                            f"На уровне {stage} дверь закрывается, появляются новые враги!",
                                            stage=stage,
                                        )

                        """
                        Старая логика респавна / не рассчитана на босса
                        """
                        # if lvl.door_x is None:
                        #     # обычный уровень без двери: волна врагов каждые RESPAWN_INTERVAL, пока враги ещё есть
                        #     if lvl.enemies_alive() and now - lvl.last_respawn >= RESPAWN_INTERVAL:
                        #         lvl.enemies = self.generate_enemies(stage)
                        #         lvl.last_enemy_attack = now
                        #         lvl.last_respawn = now
                        #         self.broadcast_event(f"Враги на уровне {stage} возродились!", stage=stage)
                        # else:
                        #     # уровень с дверью: каждые DOOR_RESPAWN_INTERVAL после зачистки появляется новая волна,
                        #     # дверь закрывается, пока враги живы
                        #     if (not lvl.enemies_alive()) and now - lvl.last_respawn >= DOOR_RESPAWN_INTERVAL:
                        #         lvl.enemies = self.generate_enemies(stage)
                        #         lvl.last_enemy_attack = now
                        #         lvl.last_respawn = now
                        #         lvl.door_open = False
                        #         self.broadcast_event(f"На уровне {stage} дверь захлопнулась, враги вернулись!", stage=stage)


                    # обновляем состояние для всех уровней, где есть игроки
                    stages = {p.stage for p in self.players.values()}
                    for st in stages:
                        self.broadcast_state_for_level(st)
            except Exception:
                traceback.print_exc()


    def run(self, host="0.0.0.0", port=5000):
        tick_thread = threading.Thread(target=self.tick_loop, daemon=True)
        tick_thread.start()

        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind((host, port))
            s.listen()
            print(f"Сервер запущен на {host}:{port}", flush=True)
            while True:
                conn, addr = s.accept()
                # отключаем Nagle, чтобы уменьшить задержки отправки маленьких пакетов
                try:
                    conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                except Exception:
                    pass
                f = conn.makefile("r", encoding="utf-8")
                try:
                    hello = recv_json_line(f)
                    if not hello or hello.get("type") != "hello":
                        conn.close()
                        continue
                    name = hello.get("name", f"Player{self.next_player_id}")
                    cls = hello.get("class", "воин")
                    with self.lock:
                        pid = self.next_player_id
                        self.next_player_id += 1
                        player = Player(pid, name, cls, conn, f)
                        self.create_player_stats(player)
                        self.players[pid] = player
                    t = threading.Thread(target=self.client_thread, args=(player,), daemon=True)
                    t.start()
                except Exception:
                    traceback.print_exc()
                    conn.close()


if __name__ == "__main__":
    host = "0.0.0.0"
    port = 5000
    if len(sys.argv) >= 2:
        host = sys.argv[1]
    if len(sys.argv) >= 3:
        port = int(sys.argv[2])
    server = GameServer()
    server.run(host, port)
