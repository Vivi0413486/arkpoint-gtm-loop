#!/usr/bin/env python3
"""GTM 빈칸 루프(v5) 결정적 검문기 — ledger.csv를 검사하고 VSR·도달·H-G·트리거 농축도(Lift)·채널 지표를 출력한다.

사용: python3 validate_ledger.py ledger.csv [--stats channel_stats.csv] [--pop population.csv]
                                 [--content content_log.csv] [--guard guardrail_log.csv]
                                 [--now 2026-10-28T23:00:00] [--ad-cap 금액]
  ledger.csv: 신청 병원 1곳 = 1행 (우편·아웃바운드가 없으므로 원장은 인바운드 신청만 담는다)
  channel_stats.csv: source,spend_krw,visits  (채널 비용·UTM 방문 수. 어필리에이트 정산액은 spend에 포함)
  population.csv: date,n_scanned,n_trig,n_t1,n_t3  (Trigger Watcher가 매일 스캔한 모집단 규모)
  content_log.csv: date,post_url,region,specialty,cell_id,keyword,kw_type,published_at,
                   views_cum,search_views_cum,top_query,source_url  (빈칸 글 1편 × 하루 = 1행, 누적값)
  guardrail_log.csv: date,channel,item,count  (원장으로 판정 못 하는 가드레일 수동 기록)
  --now: 미전달 SLA 초과 판정 기준 시각 (기본: 현재 시각)
  --ad-cap: 광고 7일 상한(원). 없으면 환경변수 GTM_AD_CAP_7D_KRW. 병원가 비공개(D6)라 코드에 적지 않는다
종료 코드: 0 = 위반 없음, 1 = 위반 있음 (다음 날 조정 전에 수정 필요)
"""
import csv
import os
import re
import sys
from collections import Counter, defaultdict
from datetime import datetime, timedelta
from math import comb

# 스펙(gtm-loop.spec.yaml)의 값과 동일하게 유지
MAX = {"c1": 25, "c2": 25, "c3": 20, "c4": 15, "c5": 15}
GATES = ("g1", "g2", "g3", "g4", "g5")
GATE_VALUES = {"PASS", "FAIL", "NA"}
EXCLUDED_SOURCES = {"cso_eum"}   # 이음 CSO 경유는 기록만, 실험 집계 전체에서 제외
SLA_BUSINESS_DAYS = 3            # R-05: 신청 완료 후 3영업일 내 이메일 전달
TARGET_HOURS = 48                # 루프 자체 목표 (달성률만 보고)
SAMPLE_DAILY_CAP = 10            # D1 확정 (10/24): 샘플 일일 제작 상한
BOT_FLAGS = {"disposable_email", "place_mismatch", "same_email_multi", "burst_submit"}
BOT_RATE_MAX, BOT_MIN_SAMPLE = 0.30, 5
HASH_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TRIGGER_DAYS = {"T1": 90, "T3": 30}   # 트리거별 유효기간(일). T2(채용공고)는 10/24 결정으로 제외
TRIGGERS = set(TRIGGER_DAYS) | {"none"}
C2_RULE = {"T1": 25, "T3": 22, "none": 0}
LIFT_SUPPORT, P_SUPPORT, MIN_N = 2.0, 0.10, 5
MIN_HITS = 2                     # 모집단 비율이 낮으면 1건만으로 p<0.10이 나오므로 지지에는 최소 2건
AD_PREFIX = "sa_"                # 검색광고 소스 (sa_t1, sa_t3, sa_gap)
AD_CAP_ENV = "GTM_AD_CAP_7D_KRW"  # D3: 7일 상한 = R-04 주3회 병원가(첫 달) × 7일 목표 유료 신청 1건, 값은 실행 시 주입
# v5 빈칸 글·도달 (스펙 content 블록과 동일하게 유지)
POST_DAILY_CAP = 3               # 빈칸 글 일 발행 상한
PROVEN_MIN_SEARCH_VIEWS = 20     # 증명된 칸: 발행 7일 이내 검색 유입 조회 합 하한 (가설, D3에 한 번만 조정)
PROVEN_WINDOW_DAYS = 7
HG_ELIGIBLE_DAYS, HG_MIN_CELLS, HG_SUPPORT_RATIO = 4, 5, 0.30   # H-G: 첫 발행 4일 경과 칸 5개 이상에서 증명 비율 30%
PRUNE_AGE_DAYS, PRUNE_MIN_POSTS, PRUNE_RATIO = 3, 3, 0.5        # 질문 유형 가지치기 신호
CONTENT_COLS = ("date", "post_url", "region", "specialty", "cell_id", "keyword", "kw_type",
                "published_at", "views_cum", "search_views_cum", "top_query", "source_url")


def grade(score):
    return "A" if score >= 70 else "B" if score >= 50 else "C"


def ts(value):
    return datetime.fromisoformat(value) if value else None


def add_business_days(start, days):
    # 주말만 제외 (공휴일은 운영자가 수동 예외 처리)
    cur = start
    while days > 0:
        cur += timedelta(days=1)
        if cur.weekday() < 5:
            days -= 1
    return cur


def trigger_valid_at_request(r):
    # 신청 시점에 트리거가 유효기간 안이었는가 (모집단 스캔과 같은 규칙으로 판정)
    if r["trigger"] not in TRIGGER_DAYS or not (r["trigger_date"] and r["sample_requested_at"]):
        return False
    age = ts(r["sample_requested_at"]) - ts(r["trigger_date"])
    return timedelta(0) <= age <= timedelta(days=TRIGGER_DAYS[r["trigger"]])


def c3_expected(r):
    # 신청 시점에 남은 유효기간 비율로 신선도 점수 계산 (스펙 C3)
    if not trigger_valid_at_request(r):
        return 0
    days = TRIGGER_DAYS[r["trigger"]]
    left = 1 - (ts(r["sample_requested_at"]) - ts(r["trigger_date"])).total_seconds() / (days * 86400)
    return 20 if left >= 0.75 else 14 if left >= 0.50 else 8 if left >= 0.25 else 0


def is_vsr(r):
    # 하드 게이트 전부 PASS + 샘플 신청 존재. 에이전트 점수는 쓰지 않는다
    return all(r[g] == "PASS" for g in GATES) and bool(r["sample_requested_at"])


def is_tvr(r):
    # TVR(하위 지표): 신청 시점에 트리거 유효기간 안이었던 병원의 VSR
    return is_vsr(r) and trigger_valid_at_request(r)


def binom_greater(k, n, p):
    # 한쪽 이항검정: 신청 n건 중 트리거 병원이 k건 이상 나올 확률 (H0: 신청 병원의 트리거 비율 = 모집단 비율 p)
    return sum(comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k, n + 1))


def lift(k, n, p0):
    return ((k + 0.5) / (n + 1)) / p0   # 0.5 보정 (k=0에서도 값이 나오게)


def supported(k, n, p0):
    return k >= MIN_HITS and lift(k, n, p0) >= LIFT_SUPPORT and binom_greater(k, n, p0) < P_SUPPORT


def k_needed(n, p0):
    # 현재 신청 수 n과 모집단 비율 p0에서 '지지'에 필요한 최소 트리거 신청 수
    return next((k for k in range(n + 1) if supported(k, n, p0)), None)


def enrichment(label, rows, hit, p0):
    n, k = len(rows), sum(hit(r) for r in rows)
    print(f"{label}: 모집단 안 검증 신청 {n}건 중 트리거 {k}건", end="")
    if p0 is None:
        print(" → 판정 보류 (모집단 스캔 기록 없음)")
        return
    if p0 <= 0:
        print(" → 판정 보류 (모집단 트리거 비율 0)")
        return
    if n < MIN_N:
        verdict = "표본 부족"
    elif supported(k, n, p0):
        verdict = "지지"
    else:
        verdict = "미확정 (7일 재측정)"
    goal_n = max(n, MIN_N)
    print(f" | 모집단 비율 {p0:.1%} | Lift {lift(k, n, p0):.2f} | p={binom_greater(k, n, p0):.3f} → {verdict}"
          f" | 지지 문턱: 신청 {goal_n}건 중 {k_needed(goal_n, p0)}건")


def check_content(path, now, errors):
    # 빈칸 글 도달 기록 검사 + L0 지표·H-G 판정·가지치기 신호 출력
    reader = csv.DictReader(open(path, encoding="utf-8"))
    print("== L0 빈칸 글·도달 ==")
    missing = [c for c in CONTENT_COLS if c not in (reader.fieldnames or [])]
    if missing:
        errors.append(f"도달 기록: 열 누락 {missing}")
        return
    rows = list(reader)
    if not rows:
        print("빈칸 글 기록 없음")
        return
    posts = defaultdict(list)
    for i, r in enumerate(rows, start=2):
        tag = f"도달 행{i}({r.get('post_url')})"
        # 열 개수가 모자란 행은 값이 None으로 들어온다 → 빈 문자열로 맞춘 뒤 필수 값 검사
        r = {c: (r.get(c) or "").strip() for c in CONTENT_COLS}
        if not all(r[c] for c in ("date", "post_url", "region", "cell_id", "kw_type", "published_at")):
            errors.append(f"{tag}: 필수 값 누락")
            continue
        try:
            views, search = int(r["views_cum"] or 0), int(r["search_views_cum"] or 0)
            day, pub = ts(r["date"]), ts(r["published_at"])
        except ValueError as e:
            errors.append(f"{tag}: 숫자·날짜 형식 오류 ({e})")
            continue
        if day > now:
            continue   # --now 이후 기록은 집계하지 않음
        if not r["source_url"].startswith("http"):
            errors.append(f"가드레일: {tag} 공공 출처 URL 없음 → 글 정지")
        if search > views:
            errors.append(f"{tag}: 검색 유입 {search} > 전체 조회 {views}")
        if day.date() < pub.date():
            errors.append(f"{tag}: 기록일이 발행일보다 이름")
        posts[r["post_url"]].append(r)

    latest, in_window = {}, {}
    for url, rs in posts.items():
        rs.sort(key=lambda r: r["date"])
        dates = [r["date"] for r in rs]
        if len(set(dates)) != len(dates):
            errors.append(f"도달 {url}: 같은 날 행이 2개 이상 (글마다 하루 1행)")
        for col in ("cell_id", "region", "published_at", "kw_type"):
            if len({r[col] for r in rs}) > 1:
                errors.append(f"도달 {url}: {col}이 행마다 다름")
        for a, b in zip(rs, rs[1:]):
            for col in ("views_cum", "search_views_cum"):
                if int(b[col] or 0) < int(a[col] or 0):
                    errors.append(f"도달 {url}: {col} 누적값이 {a['date']}→{b['date']}에 줄어듦")
        latest[url] = rs[-1]
        limit = (ts(rs[0]["published_at"]) + timedelta(days=PROVEN_WINDOW_DAYS)).date()
        window = [r for r in rs if ts(r["date"]).date() <= limit]
        in_window[url] = window

    # 일 발행 상한 (발행일 기준 글 수)
    for day, n in Counter(ts(r["published_at"]).date() for r in latest.values()).items():
        if n > POST_DAILY_CAP:
            errors.append(f"가드레일: {day} 빈칸 글 {n}편 발행 > 상한 {POST_DAILY_CAP}편")

    # 칸별 집계: 증명 = 발행 7일 이내 검색 유입 합 ≥ 하한 AND 유입 검색어에 지역어 포함
    cells = defaultdict(lambda: {"first": None, "search": 0, "local_query": False, "region": ""})
    for url, r in latest.items():
        c = cells[r["cell_id"]]
        pub = ts(r["published_at"])
        c["first"] = pub if c["first"] is None else min(c["first"], pub)
        c["region"] = r["region"]
        window = in_window[url]
        c["search"] += int(window[-1]["search_views_cum"] or 0) if window else 0
        c["local_query"] |= any(r["region"] in w["top_query"] for w in window)
    proven = {cid for cid, c in cells.items() if c["search"] >= PROVEN_MIN_SEARCH_VIEWS and c["local_query"]}
    eligible = {cid for cid, c in cells.items() if c["first"] <= now - timedelta(days=HG_ELIGIBLE_DAYS)}

    reach = sum(int(r["search_views_cum"] or 0) for r in latest.values())
    views = sum(int(r["views_cum"] or 0) for r in latest.values())
    print(f"발행: 글 {len(latest)}편 / 칸 {len(cells)}개")
    print(f"환자 도달(검색 유입 조회 누적): {reach}회 / 전체 조회 {views}회 (조회수이며 사람 수 아님)")
    print(f"증명된 칸: {len(proven)}개 " + (f"({', '.join(sorted(proven))})" if proven else ""))

    # H-G 판정: 첫 발행 후 4일이 지난 칸 중 증명된 칸 비율
    n, k = len(eligible), len(eligible & proven)
    if n < HG_MIN_CELLS:
        verdict = "표본 부족"
    elif k / n >= HG_SUPPORT_RATIO:
        verdict = "지지"
    else:
        verdict = "미확정 (7일 재측정)"
    ratio = f"{k / n:.0%}" if n else "-"
    print(f"H-G: 판정 대상 칸 {n}개 중 증명 {k}개 ({ratio}) → {verdict}"
          f" | 아직 판정 전 칸 {len(cells) - n}개 | 지지 기준 {HG_MIN_CELLS}칸 이상·{HG_SUPPORT_RATIO:.0%}")

    # 가지치기 신호: 발행 3일 지난 글이 3편 이상인 유형 중 글당 검색 유입이 전체 평균의 절반 미만
    aged = [r for r in latest.values() if ts(r["published_at"]) <= now - timedelta(days=PRUNE_AGE_DAYS)]
    if aged:
        overall = sum(int(r["search_views_cum"] or 0) for r in aged) / len(aged)
        by_type = defaultdict(list)
        for r in aged:
            by_type[r["kw_type"]].append(int(r["search_views_cum"] or 0))
        print("질문 유형 | 글(3일 경과) | 글당 검색 유입")
        signals = []
        for t, vs in sorted(by_type.items()):
            avg = sum(vs) / len(vs)
            print(f"{t} | {len(vs)} | {avg:.1f}")
            if len(vs) >= PRUNE_MIN_POSTS and avg < overall * PRUNE_RATIO:
                signals.append(f"조정 신호: '{t}' 글당 {avg:.1f} < 전체 평균 {overall:.1f}의 절반 → 다음 날부터 발행 중단")
        for s in signals:
            print(s)


def main(argv):
    opts = {}
    for flag in ("--stats", "--pop", "--content", "--guard", "--now", "--ad-cap"):
        if flag in argv:
            i = argv.index(flag)
            opts[flag] = argv[i + 1]
            argv = argv[:i] + argv[i + 2:]
    now = datetime.fromisoformat(opts["--now"]) if "--now" in opts else datetime.now()
    all_rows = list(csv.DictReader(open(argv[0], encoding="utf-8")))
    errors = []

    # 병원당 1회: ykiho·플레이스 주소 기준 중복 차단
    for key in ("ykiho", "place_url"):
        for k, n in Counter(r[key] for r in all_rows if r[key]).items():
            if n > 1:
                errors.append(f"중복 {key}={k}")

    for i, r in enumerate(all_rows, start=2):
        tag = f"행{i}({r['ykiho']})"
        if not r["ykiho"] or not r["name"]:
            errors.append(f"{tag}: ykiho/병원명 누락")
        for g in GATES:
            if r[g] not in GATE_VALUES:
                errors.append(f"{tag}: {g} 값 '{r[g]}' 허용 외")
        if r["g1"] == "PASS" and not HASH_RE.match(r["evidence_hash"]):
            errors.append(f"{tag}: G1 PASS인데 심평원 응답 해시가 sha256 형식이 아님")
        if r["in_pop"] not in ("0", "1"):
            errors.append(f"{tag}: in_pop 값 '{r['in_pop']}' 허용 외 (0/1)")
        flags = [f for f in r["bot_flags"].split("|") if f]
        for f in flags:
            if f not in BOT_FLAGS:
                errors.append(f"{tag}: 봇 플래그 '{f}' 허용 외")
        if len(flags) >= 2 and r["g5"] == "PASS":
            errors.append(f"{tag}: 봇 플래그 {len(flags)}개인데 G5 PASS")
        if r["score"]:
            parts = {c: int(r[c] or 0) for c in MAX}
            for c, v in parts.items():
                if not 0 <= v <= MAX[c]:
                    errors.append(f"{tag}: {c}={v} 배점 범위 초과")
            if sum(parts.values()) != int(r["score"]):
                errors.append(f"{tag}: score 합계 불일치")
            if r["grade"] != grade(int(r["score"])):
                errors.append(f"{tag}: 등급 불일치")
            if r["trigger"] in C2_RULE and parts["c2"] != C2_RULE[r["trigger"]]:
                errors.append(f"{tag}: c2={parts['c2']} 트리거 강도 규칙과 불일치")
            if r["sample_requested_at"] and parts["c3"] != c3_expected(r):
                errors.append(f"{tag}: c3={parts['c3']} 신선도 재계산 {c3_expected(r)}과 불일치")
        req, sent = ts(r["sample_requested_at"]), ts(r["sample_sent_at"])
        if req and is_vsr(r):
            deadline = add_business_days(req, SLA_BUSINESS_DAYS)
            if (sent or now) > deadline:
                state = "전달" if sent else "미전달"
                errors.append(f"{tag}: 샘플 {state} 3영업일 SLA 초과 (기한 {deadline:%m-%d %H:%M})")
        if sent and not r["sample_hours"]:
            errors.append(f"{tag}: 샘플 전달했는데 제작시간 미기록")
        # 트리거 무결성: 신청 병원도 모집단과 같은 규칙·같은 증거 형식으로 분류
        if r["trigger"] not in TRIGGERS:
            errors.append(f"{tag}: trigger 값 '{r['trigger']}' 허용 외")
        elif r["trigger"] != "none":
            if not (r["trigger_date"] and r["trigger_evidence"] and r["detected_at"]):
                errors.append(f"{tag}: {r['trigger']}인데 트리거 날짜·증거·분류 시각 누락")
            elif not HASH_RE.match(r["trigger_evidence"]):
                errors.append(f"{tag}: 트리거 증거가 sha256 해시 형식이 아님")

    # 이하 집계는 실험 채널만 (cso_eum 제외)
    rows = [r for r in all_rows if r["source"] not in EXCLUDED_SOURCES]
    stats = {}
    if "--stats" in opts:
        stats = {s["source"]: s for s in csv.DictReader(open(opts["--stats"], encoding="utf-8"))}
    p0 = {}
    scanned = 0
    if "--pop" in opts:
        pop = list(csv.DictReader(open(opts["--pop"], encoding="utf-8")))
        for p in pop:
            s, t, t1, t3 = (int(p[c]) for c in ("n_scanned", "n_trig", "n_t1", "n_t3"))
            if not (max(t1, t3) <= t <= min(t1 + t3, s)):
                errors.append(f"모집단 {p['date']}: n_trig={t}가 n_t1·n_t3·n_scanned와 맞지 않음")
        scanned = sum(int(p["n_scanned"]) for p in pop)
        if scanned:
            p0 = {key: sum(int(p[col]) for p in pop) / scanned
                  for key, col in (("all", "n_trig"), ("T1", "n_t1"), ("T3", "n_t3"))}

    if "--content" in opts:
        check_content(opts["--content"], now, errors)

    inbound = [r for r in rows if r["g4"] != "NA"]
    vsr = [r for r in rows if is_vsr(r)]
    tvr = [r for r in rows if is_tvr(r)]
    sent = [r for r in vsr if r["sample_sent_at"]]
    print("== 퍼널 ==")
    if p0:
        print(f"L1 감지: 모집단 스캔 누적 {scanned}건, 트리거 비율 {p0['all']:.1%} (T1 {p0['T1']:.1%} / T3 {p0['T3']:.1%})")
    else:
        print("L1 감지: 모집단 스캔 기록 없음")
    visits = sum(int(s.get("visits") or 0) for src, s in stats.items() if src not in EXCLUDED_SOURCES)
    print(f"L2 UTM 방문: {visits if stats else '채널 통계 없음'}")
    print(f"L3 신청: {len(inbound)} / L4 검증 신청(VSR, NSM): {len(vsr)}")
    print(f"L5 TVR: {len(tvr)} (" + ", ".join(f"{k} {sum(r['trigger'] == k for r in tvr)}" for k in TRIGGER_DAYS) + ")")
    on_time = sum((ts(r["sample_sent_at"]) - ts(r["sample_requested_at"])).total_seconds() <= TARGET_HOURS * 3600
                  for r in sent)
    print(f"L6 샘플 전달: {len(sent)} (48h 목표 달성 {on_time}/{len(sent)})")
    print(f"L7 결과 확인: {sum(bool(r['result_checked_at']) for r in sent)} / 전달 {len(sent)}")
    print(f"L8 유료 신청: {sum(bool(r['paid_applied_at']) for r in vsr)}")
    print(f"제외(이음 CSO 경유): {len(all_rows) - len(rows)}행")

    # 소스별 판단표 (B-00 C1: 유료 전환·획득 비용·지원 부담)
    by_src = defaultdict(list)
    for r in vsr:
        by_src[r["source"]].append(r)
    print("== 소스 판단표 ==")
    print("source | VSR | TVR | 유료신청 | 평균제작h | CPVSR | 채널비용/유료신청 | 봇률")
    for src in sorted(set(by_src) | {r["source"] for r in inbound} | {s for s in stats if s not in EXCLUDED_SOURCES}):
        v = by_src.get(src, [])
        paid = sum(bool(r["paid_applied_at"]) for r in v)
        hours = [float(r["sample_hours"]) for r in v if r["sample_hours"]]
        spend = int(stats[src]["spend_krw"] or 0) if src in stats else None
        src_in = [r for r in inbound if r["source"] == src]
        bots = sum(r["g5"] == "FAIL" for r in src_in)
        line = f"{src} | {len(v)} | {sum(is_tvr(r) for r in v)} | {paid} | "
        line += f"{sum(hours) / len(hours):.1f}" if hours else "-"
        line += f" | {spend // len(v):,}원" if spend is not None and v else " | -"
        line += f" | {spend // paid:,}원" if spend is not None and paid else " | -"
        line += f" | {bots}/{len(src_in)}" if src_in else " | -"
        print(line)
        if len(src_in) >= BOT_MIN_SAMPLE and bots / len(src_in) > BOT_RATE_MAX:
            errors.append(f"가드레일: {src} 봇률 {bots / len(src_in):.0%} > 30% → 소스 정지")

    # H-T 판정: 신청 병원의 트리거 비율이 모집단 비율의 2배 이상인가 (모집단 안 신청만)
    print("== H-T 트리거 농축도 (방향 판단용) ==")
    in_pop = [r for r in vsr if r["in_pop"] == "1"]
    enrichment("전체", in_pop, trigger_valid_at_request, p0.get("all"))
    for k in TRIGGER_DAYS:
        enrichment(k, in_pop, lambda r, k=k: r["trigger"] == k and trigger_valid_at_request(r), p0.get(k))

    # 광고 예산 상한과 손절 신호 (D3)
    print("== 광고 예산 ==")
    ad_spend = sum(int(s["spend_krw"] or 0) for src, s in stats.items() if src.startswith(AD_PREFIX))
    # v5: GAP 그룹은 트리거 병원만 노리지 않으므로 손절 기준을 광고 TVR → 광고 VSR로 변경
    ad_vsr = sum(r["source"].startswith(AD_PREFIX) for r in vsr)
    ad_cap = int(opts.get("--ad-cap") or os.environ.get(AD_CAP_ENV) or 0) or None
    if ad_cap is None:
        # 상한 없이 광고비가 나가면 D3 위반으로 본다
        print(f"광고 지출 {ad_spend:,}원 / 7일 상한 미설정 | 광고 VSR {ad_vsr}")
        if ad_spend > 0:
            errors.append(f"가드레일: 7일 상한 미설정 상태로 광고 지출 {ad_spend:,}원 (--ad-cap 또는 {AD_CAP_ENV} 필요)")
    else:
        print(f"광고 지출 {ad_spend:,}원 / 7일 상한 {ad_cap:,}원 | 광고 VSR {ad_vsr}")
        if ad_spend > ad_cap:
            errors.append(f"가드레일: 광고 지출 {ad_spend:,}원이 7일 상한 {ad_cap:,}원 초과")
        elif ad_spend >= ad_cap // 2 and ad_vsr == 0:
            print("조정 신호: 상한의 절반을 썼는데 광고 VSR 0 → 광고 정지")
    pending = [r for r in rows if is_vsr(r) and not r["sample_sent_at"]]
    if len(pending) > SAMPLE_DAILY_CAP * 2:
        print(f"조정 신호: 샘플 대기열 {len(pending)}건 > 상한 {SAMPLE_DAILY_CAP}×2 → 광고 50% 감액")

    if "--guard" in opts:
        for g in csv.DictReader(open(opts["--guard"], encoding="utf-8")):
            if int(g["count"] or 0) > 0:
                errors.append(f"가드레일: {g['date']} {g['channel']} {g['item']} {g['count']}건 → 채널 정지")

    print("== 위반 ==")
    for e in errors:
        print("FAIL", e)
    print(f"총 {len(errors)}건")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
