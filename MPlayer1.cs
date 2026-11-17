using System.Collections.Generic;

namespace CardFool
{
    public class MPlayer1
    {
        private string Name = "Kotom";                          // имя игрока
        private List<SCard> hand = new List<SCard>();              // карты на руке
        private SCard trump;                                        // козырь
        private int player2_cards = 6;                              // оценка карт у противника
        private int coloda = 24;                                    // оценка карт в колоде
        private List<SCard> dump = new List<SCard>();              // все карты в сбросе (бито)
        private List<SCard> oppKnown = new List<SCard>();          // карты, которые точно у противника
        private int stage = 1;                                      // стадия игры (1..4 по колоде)
        private bool iAmAttacker;                                   // моя роль в текущем раунде

        // пороги защиты подобраны grid search
        private const int Rule1ColodaMin = 6;        // экономия 2+ козырей
        private const int Rule2ColodaMin = 4;        // экономия старших козырей
        private const int Rule3ColodaMin = 6;        // экономия козыря на картинку
        private const int SafetyEndgameColoda = 4;   // эндгейм
        private const int SafetyMaxHandIfTake = 11;  // лимит на взятие
        private const int Stage4MinimaxDepth = 6;    // глубина минимакса


        // имя игрока
        public string GetName()
        {
            return Name;
        }

        // сколько у меня карт
        public int GetCount()
        {
            return hand.Count;
        }

        // старт партии запоминаем козырь сбрасываем учёт
        public void SetTrump(SCard NewTrump)
        {
            trump = NewTrump;
            coloda = 24;
            player2_cards = 6;
            hand.Clear();
            dump.Clear();
            oppKnown.Clear();
        }

        // карта пришла мне из колоды или со стола
        public void AddToHand(SCard card)
        {
            hand.Add(card);
            RemoveCardFromList(oppKnown, card);
        }

        // равенство карт по масти и рангу
        private static bool SameCard(SCard a, SCard b)
        {
            return a.Suit == b.Suit && a.Rank == b.Rank;
        }

        // удалить первую найденную карту c из списка
        private static bool RemoveCardFromList(List<SCard> list, SCard c)
        {
            for (int i = 0; i < list.Count; i++)
            {
                if (SameCard(list[i], c)) { list.RemoveAt(i); return true; }
            }
            return false;
        }

        // есть ли карта c в списке
        private static bool ListContainsCard(List<SCard> list, SCard c)
        {
            for (int i = 0; i < list.Count; i++)
            {
                if (SameCard(list[i], c)) return true;
            }
            return false;
        }

        // сколько карт лежит на столе нижние плюс отбитые верхние
        private static int CountTableCards(List<SCardPair> table)
        {
            int n = 0;
            for (int i = 0; i < table.Count; i++)
            {
                n++;
                if (table[i].Beaten) n++;
            }
            return n;
        }

        // сколько неотбитых пар на столе
        private static int CountUnbeaten(List<SCardPair> table)
        {
            int n = 0;
            for (int i = 0; i < table.Count; i++) if (!table[i].Beaten) n++;
            return n;
        }

        // оценка размера руки оппа через закон сохранения 36 карт
        private void UpdateOppCount(List<SCardPair> table)
        {
            int onTable = CountTableCards(table);
            player2_cards = 36 - hand.Count - dump.Count - coloda - onTable;
            if (player2_cards < 0) player2_cards = 0;
        }

        // стадия игры по размеру колоды
        private void UpdateStage()
        {
            if (coloda > 12) stage = 1;
            else if (coloda > 4) stage = 2;
            else if (coloda > 0) stage = 3;
            else stage = 4;
        }

        // точная рука оппа работает только в эндгейме
        private List<SCard> ComputeOppExactHand(List<SCardPair> table)
        {
            List<SCard> onTableList = new List<SCard>();
            for (int i = 0; i < table.Count; i++)
            {
                onTableList.Add(table[i].Down);
                if (table[i].Beaten) onTableList.Add(table[i].Up);
            }
            List<SCard> opp = new List<SCard>();
            for (int s = 0; s <= 3; s++)
            {
                for (int r = 6; r <= 14; r++)
                {
                    SCard c = new SCard((Suits)s, r);
                    if (ListContainsCard(hand, c)) continue;
                    if (ListContainsCard(dump, c)) continue;
                    if (ListContainsCard(onTableList, c)) continue;
                    opp.Add(c);
                }
            }
            return opp;
        }

        // может ли опп побить одну атаку atk
        private bool CanOppBeat(SCard atk, List<SCard> oppCards)
        {
            for (int i = 0; i < oppCards.Count; i++)
            {
                SCard c = oppCards[i];
                if (c.Suit == atk.Suit && c.Rank > atk.Rank) return true;
                if (atk.Suit != trump.Suit && c.Suit == trump.Suit) return true;
            }
            return false;
        }

        // все комбинации size карт из группы рекурсивно
        private void GenerateCombinations(List<SCard> group, int size, int start,
                                          List<SCard> current, List<List<SCard>> result)
        {
            if (current.Count == size)
            {
                result.Add(new List<SCard>(current));
                return;
            }
            for (int i = start; i < group.Count; i++)
            {
                current.Add(group[i]);
                GenerateCombinations(group, size, i + 1, current, result);
                current.RemoveAt(current.Count - 1);
            }
        }

        // точная проверка может ли опп отбить все атаки разными картами 
        private bool CanOppDefendAll(List<SCard> subset, List<SCard> oppCards)
        {
            int n = subset.Count;
            int m = oppCards.Count;
            if (m < n) return false;

            int[] matchR = new int[m];
            for (int j = 0; j < m; j++) matchR[j] = -1;

            for (int i = 0; i < n; i++)
            {
                bool[] visited = new bool[m];
                if (!TryAugmentDefence(i, subset, oppCards, matchR, visited)) return false;
            }
            return true;
        }

        // поиск увеличивающей цепочки в bipartite
        private bool TryAugmentDefence(int i, List<SCard> subset, List<SCard> oppCards,
                                       int[] matchR, bool[] visited)
        {
            SCard atk = subset[i];
            for (int j = 0; j < oppCards.Count; j++)
            {
                if (visited[j]) continue;
                SCard c = oppCards[j];
                bool sameSuit = c.Suit == atk.Suit && c.Rank > atk.Rank;
                bool trumpBeat = atk.Suit != trump.Suit && c.Suit == trump.Suit;
                if (!sameSuit && !trumpBeat) continue;
                visited[j] = true;
                if (matchR[j] == -1 || TryAugmentDefence(matchR[j], subset, oppCards, matchR, visited))
                {
                    matchR[j] = i;
                    return true;
                }
            }
            return false;
        }

        // минимальная карта в h которая бьёт target
        private int FindMinBeatIn(SCard target, List<SCard> h)
        {
            int bestSameIdx = -1, bestSameRank = 0;
            int bestTrumpIdx = -1, bestTrumpRank = 0;
            for (int i = 0; i < h.Count; i++)
            {
                SCard c = h[i];
                if (c.Suit == target.Suit && c.Rank > target.Rank)
                {
                    if (bestSameIdx == -1 || c.Rank < bestSameRank) { bestSameIdx = i; bestSameRank = c.Rank; }
                }
                else if (target.Suit != trump.Suit && c.Suit == trump.Suit)
                {
                    if (bestTrumpIdx == -1 || c.Rank < bestTrumpRank) { bestTrumpIdx = i; bestTrumpRank = c.Rank; }
                }
            }
            if (bestSameIdx != -1) return bestSameIdx;
            return bestTrumpIdx;
        }

        // план защиты или null если отбить нечем
        private List<KeyValuePair<int, SCard>> BuildDefencePlan(List<SCardPair> table)
        {
            List<int> unbeatenIdx = new List<int>();
            for (int i = 0; i < table.Count; i++) if (!table[i].Beaten) unbeatenIdx.Add(i);

            unbeatenIdx.Sort(delegate (int a, int b)
            {
                bool aT = table[a].Down.Suit == trump.Suit;
                bool bT = table[b].Down.Suit == trump.Suit;
                if (aT != bT)
                {
                    if (aT) return -1;
                    return 1;
                }
                return table[b].Down.Rank - table[a].Down.Rank;
            });

            List<SCard> tmp = new List<SCard>(hand);
            List<KeyValuePair<int, SCard>> plan = new List<KeyValuePair<int, SCard>>();
            for (int i = 0; i < unbeatenIdx.Count; i++)
            {
                int idx = unbeatenIdx[i];
                SCard target = table[idx].Down;
                int beatIdx = FindMinBeatIn(target, tmp);
                if (beatIdx == -1) return null;
                SCard beat = tmp[beatIdx];
                plan.Add(new KeyValuePair<int, SCard>(idx, beat));
                tmp.RemoveAt(beatIdx);
            }
            return plan;
        }

        // все ходы атакующего multicard сначала по убыванию размера потом одиночки
        private List<List<SCard>> EnumerateAttackMoves(List<SCard> handCards)
        {
            List<List<SCard>> moves = new List<List<SCard>>();
            for (int size = MGameRules.TotalCards; size >= 2; size--)
            {
                for (int r = 6; r <= 14; r++)
                {
                    List<SCard> group = new List<SCard>();
                    for (int i = 0; i < handCards.Count; i++)
                        if (handCards[i].Rank == r && handCards[i].Suit != trump.Suit) group.Add(handCards[i]);
                    if (group.Count < size) continue;
                    List<List<SCard>> combos = new List<List<SCard>>();
                    GenerateCombinations(group, size, 0, new List<SCard>(), combos);
                    moves.AddRange(combos);
                }
            }
            for (int r = 6; r <= 14; r++)
            {
                for (int i = 0; i < handCards.Count; i++)
                    if (handCards[i].Rank == r) moves.Add(new List<SCard>() { handCards[i] });
            }
            return moves;
        }

        // удаляет из hand карты из remove возвращает копию
        private static List<SCard> SubtractCards(List<SCard> hand, List<SCard> remove)
        {
            List<SCard> result = new List<SCard>(hand);
            for (int i = 0; i < remove.Count; i++) RemoveCardFromList(result, remove[i]);
            return result;
        }

        // жадная защита для каждой атаки минимальный беат
        private List<SCard> GreedyDefense(List<SCard> attack, List<SCard> defHand)
        {
            List<SCard> tmp = new List<SCard>(defHand);
            List<SCard> resp = new List<SCard>();
            for (int i = 0; i < attack.Count; i++)
            {
                int idx = FindMinBeatIn(attack[i], tmp);
                if (idx == -1) return null;
                resp.Add(tmp[idx]);
                tmp.RemoveAt(idx);
            }
            return resp;
        }

        // минимакс эндгейма возвращает defHand минус attHand
        private int MinimaxStage4(List<SCard> attHand, List<SCard> defHand, int depth, int alpha, int beta)
        {
            if (depth <= 0 || attHand.Count == 0 || defHand.Count == 0)
                return defHand.Count - attHand.Count;

            int best = -1000;
            List<List<SCard>> moves = EnumerateAttackMoves(attHand);
            for (int mi = 0; mi < moves.Count; mi++)
            {
                List<SCard> attack = moves[mi];
                if (attack.Count > defHand.Count) continue;

                List<SCard> nAttHand = SubtractCards(attHand, attack);
                int score;
                if (!CanOppDefendAll(attack, defHand))
                {
                    List<SCard> nDefHand = new List<SCard>(defHand);
                    nDefHand.AddRange(attack);
                    score = MinimaxStage4(nAttHand, nDefHand, depth - 1, alpha, beta);
                }
                else
                {
                    List<SCard> defResp = GreedyDefense(attack, defHand);
                    if (defResp == null) continue;
                    List<SCard> nDefHand = SubtractCards(defHand, defResp);
                    score = -MinimaxStage4(nDefHand, nAttHand, depth - 1, -beta, -alpha);
                }
                if (score > best) best = score;
                if (best > alpha) alpha = best;
                if (alpha >= beta) break;
            }
            return best;
        }

        // top level минимакс возвращает лучшую атаку как список карт
        private List<SCard> MinimaxStage4PickAttack(List<SCard> attHand, List<SCard> defHand, int depth)
        {
            int bestScore = -1000;
            List<SCard> bestAttack = null;
            List<List<SCard>> moves = EnumerateAttackMoves(attHand);
            for (int mi = 0; mi < moves.Count; mi++)
            {
                List<SCard> attack = moves[mi];
                if (attack.Count > defHand.Count) continue;

                List<SCard> nAttHand = SubtractCards(attHand, attack);
                int score;
                if (!CanOppDefendAll(attack, defHand))
                {
                    List<SCard> nDefHand = new List<SCard>(defHand);
                    nDefHand.AddRange(attack);
                    score = MinimaxStage4(nAttHand, nDefHand, depth - 1, bestScore, 1000);
                }
                else
                {
                    List<SCard> defResp = GreedyDefense(attack, defHand);
                    if (defResp == null) continue;
                    List<SCard> nDefHand = SubtractCards(defHand, defResp);
                    score = -MinimaxStage4(nDefHand, nAttHand, depth - 1, -1000, -bestScore);
                }
                if (score > bestScore) { bestScore = score; bestAttack = attack; }
            }
            return bestAttack;
        }

        // моя атака в эндгейме минимакс иначе пара или минимальная не-козырная
        public List<SCard> LayCards()
        {
            iAmAttacker = true;
            UpdateOppCount(new List<SCardPair>());
            UpdateStage();
            List<SCard> chosen = new List<SCard>();
            if (hand.Count == 0) return chosen;

            int maxCanLay = MGameRules.TotalCards;
            if (player2_cards < maxCanLay) maxCanLay = player2_cards;
            if (maxCanLay < 1) maxCanLay = 1;

            if (stage == 4 && hand.Count >= 1)
            {
                List<SCard> oppExact = ComputeOppExactHand(new List<SCardPair>());
                if (oppExact.Count > 0)
                {
                    List<SCard> bestAttack = MinimaxStage4PickAttack(hand, oppExact, Stage4MinimaxDepth);
                    if (bestAttack != null) chosen.AddRange(bestAttack);
                }
            }

            if (chosen.Count == 0 && hand.Count < 3)
            {
                int maxIdx = 0;
                for (int i = 1; i < hand.Count; i++)
                    if (hand[i].Rank > hand[maxIdx].Rank) maxIdx = i;
                chosen.Add(hand[maxIdx]);
            }
            else if (chosen.Count == 0)
            {
                int bestRank = -1;
                int bestCount = 1;
                for (int r = 6; r <= 10; r++)
                {
                    int cnt = 0;
                    for (int i = 0; i < hand.Count; i++)
                    {
                        if (hand[i].Suit != trump.Suit && hand[i].Rank == r) cnt++;
                    }
                    if (cnt > bestCount) { bestCount = cnt; bestRank = r; }
                }
                if (bestRank != -1)
                {
                    for (int i = 0; i < hand.Count; i++)
                    {
                        if (hand[i].Suit != trump.Suit && hand[i].Rank == bestRank)
                        {
                            chosen.Add(hand[i]);
                            break;
                        }
                    }
                }
                else
                {
                    int minIdx = -1, minRank = 0;
                    for (int i = 0; i < hand.Count; i++)
                    {
                        if (hand[i].Suit != trump.Suit)
                        {
                            if (minIdx == -1 || hand[i].Rank < minRank) { minIdx = i; minRank = hand[i].Rank; }
                        }
                    }
                    if (minIdx == -1)
                    {
                        for (int i = 0; i < hand.Count; i++)
                        {
                            if (minIdx == -1 || hand[i].Rank < minRank) { minIdx = i; minRank = hand[i].Rank; }
                        }
                    }
                    if (minIdx != -1) chosen.Add(hand[minIdx]);
                }
            }

            for (int k = 0; k < chosen.Count; k++) RemoveCardFromList(hand, chosen[k]);
            return chosen;
        }

        // защита true отбился false беру правила экономии плюс 
        public bool Defend(List<SCardPair> table)
        {
            iAmAttacker = false;
            UpdateOppCount(table);
            UpdateStage();

            List<KeyValuePair<int, SCard>> plan = BuildDefencePlan(table);
            if (plan == null) return false;

            int tableCards = CountTableCards(table);
            int countIfTake = hand.Count + tableCards;

            int planTrumpCount = 0;
            bool planHasHighTrump = false;
            for (int k = 0; k < plan.Count; k++)
            {
                SCard beat = plan[k].Value;
                if (beat.Suit == trump.Suit)
                {
                    planTrumpCount++;
                    if (beat.Rank > 10) planHasHighTrump = true;
                }
            }

            int existingTrumpsOnTable = 0;
            for (int i = 0; i < table.Count; i++)
            {
                if (table[i].Beaten && table[i].Up.Suit == trump.Suit) existingTrumpsOnTable++;
            }

            bool doDefend = true;

            if (coloda > Rule1ColodaMin && (planTrumpCount + existingTrumpsOnTable) >= 2)
                doDefend = false;

            if (coloda > Rule2ColodaMin && planHasHighTrump)
                doDefend = false;

            if (coloda > Rule3ColodaMin && plan.Count == 1)
            {
                SCard beat = plan[0].Value;
                SCard atk = table[plan[0].Key].Down;
                if (beat.Suit == trump.Suit && atk.Rank >= 11)
                    doDefend = false;
            }

            if (planTrumpCount == 0) doDefend = true;
            if (coloda <= SafetyEndgameColoda) doDefend = true;
            if (countIfTake >= SafetyMaxHandIfTake) doDefend = true;

            if (!doDefend) return false;

            for (int k = 0; k < plan.Count; k++)
            {
                int idx = plan[k].Key;
                SCard beat = plan[k].Value;
                SCardPair np = table[idx];
                np.SetUp(beat, trump.Suit);
                table[idx] = np;
                RemoveCardFromList(hand, beat);
            }
            return true;
        }

        // подкид кандидаты по рангу со стола сортировка по силе 
        public bool AddCards(List<SCardPair> table, bool OpponentDefenced)
        {
            if (hand.Count == 0) return false;
            UpdateOppCount(table);
            UpdateStage();

            int maxAdd = MGameRules.TotalCards - table.Count;
            int otherMax = player2_cards - CountUnbeaten(table);
            if (otherMax < maxAdd) maxAdd = otherMax;
            if (maxAdd <= 0) return false;

            List<SCard> candidates = new List<SCard>();
            for (int i = 0; i < hand.Count; i++)
            {
                SCard c = hand[i];
                bool matchRank = false;
                for (int j = 0; j < table.Count; j++)
                {
                    if (table[j].Down.Rank == c.Rank) { matchRank = true; break; }
                    if (table[j].Beaten && table[j].Up.Rank == c.Rank) { matchRank = true; break; }
                }
                if (matchRank) candidates.Add(c);
            }
            if (candidates.Count == 0) return false;

            if (stage == 4)
            {
                List<SCard> oppExact = ComputeOppExactHand(table);
                candidates.Sort(delegate (SCard a, SCard b)
                {
                    bool aUnb = !CanOppBeat(a, oppExact);
                    bool bUnb = !CanOppBeat(b, oppExact);
                    if (aUnb != bUnb)
                    {
                        if (aUnb) return -1;
                        return 1;
                    }
                    int aT = 0;
                    if (a.Suit == trump.Suit) aT = 1;
                    int bT = 0;
                    if (b.Suit == trump.Suit) bT = 1;
                    if (aT != bT) return aT - bT;
                    return a.Rank - b.Rank;
                });
            }
            else
            {
                candidates.Sort(delegate (SCard a, SCard b)
                {
                    int aT = 0;
                    if (a.Suit == trump.Suit) aT = 1;
                    int bT = 0;
                    if (b.Suit == trump.Suit) bT = 1;
                    if (aT != bT) return aT - bT;
                    return a.Rank - b.Rank;
                });
            }

            int limit;
            if (OpponentDefenced)
            {
                if (stage == 4) limit = 3;
                else if (stage == 3) limit = 2;
                else limit = 1;
            }
            else
            {
                if (stage == 4) limit = 4;
                else if (stage == 3) limit = 3;
                else limit = 2;
            }
            if (limit > maxAdd) limit = maxAdd;

            List<SCard> chosen = new List<SCard>();
            for (int i = 0; i < candidates.Count && chosen.Count < limit; i++)
            {
                if (!AllowedToThrow(candidates[i])) continue;
                chosen.Add(candidates[i]);
            }
            if (chosen.Count == 0) return false;

            for (int k = 0; k < chosen.Count; k++)
            {
                RemoveCardFromList(hand, chosen[k]);
                table.Add(new SCardPair(chosen[k]));
            }
            return true;
        }

        // что разрешено подкидывать по стадии
        private bool AllowedToThrow(SCard c)
        {
            if (hand.Count < 3) return true;
            if (stage == 4) return true;
            if (stage == 1) return c.Suit != trump.Suit && c.Rank <= 10;
            if (stage == 2)
            {
                if (c.Suit == trump.Suit) return c.Rank < 10;
                return c.Rank < 12;
            }
            if (c.Suit == trump.Suit) return c.Rank <= 12;
            return true;
        }

        // конец раунда обновляем dump oppKnown coloda
        public void OnEndRound(List<SCardPair> table, bool IsDefenceSuccesful)
        {
            bool oppWasAttacker = !iAmAttacker;
            bool oppWasDefender = iAmAttacker;

            if (IsDefenceSuccesful)
            {
                for (int i = 0; i < table.Count; i++)
                {
                    SCardPair p = table[i];
                    if (!ListContainsCard(dump, p.Down)) dump.Add(p.Down);
                    if (p.Beaten && !ListContainsCard(dump, p.Up)) dump.Add(p.Up);
                    if (oppWasAttacker) RemoveCardFromList(oppKnown, p.Down);
                    if (oppWasDefender && p.Beaten) RemoveCardFromList(oppKnown, p.Up);
                }
            }
            else
            {
                if (oppWasDefender)
                {
                    for (int i = 0; i < table.Count; i++)
                    {
                        SCardPair p = table[i];
                        if (!ListContainsCard(oppKnown, p.Down)) oppKnown.Add(p.Down);
                        if (p.Beaten && !ListContainsCard(oppKnown, p.Up)) oppKnown.Add(p.Up);
                    }
                }
                else
                {
                    for (int i = 0; i < table.Count; i++)
                        RemoveCardFromList(oppKnown, table[i].Down);
                }
            }

            int myMid = hand.Count;
            int oppMid = 36 - myMid - coloda - dump.Count;
            if (oppMid < 0) oppMid = 0;

            int firstMid;
            int secondMid;
            if (iAmAttacker)
            {
                firstMid = myMid;
                secondMid = oppMid;
            }
            else
            {
                firstMid = oppMid;
                secondMid = myMid;
            }

            int firstDraw = MGameRules.TotalCards - firstMid;
            if (firstDraw < 0) firstDraw = 0;
            if (firstDraw > coloda) firstDraw = coloda;

            int deckMid = coloda - firstDraw;
            int secondDraw = MGameRules.TotalCards - secondMid;
            if (secondDraw < 0) secondDraw = 0;
            if (secondDraw > deckMid) secondDraw = deckMid;

            coloda = coloda - firstDraw - secondDraw;
            if (coloda < 0) coloda = 0;
        }
    }
}
