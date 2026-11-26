// Certify lower bounds on intersection counts on the closed genus-two surface.
// Every successful geometry test gives an upper bound on graph distance.
// A SURVIVOR requests a separate exact-distance test. C++17, no dependencies.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

using List = std::vector<int>;
using Six = std::array<int, 6>;
using Twelve = std::array<int, 12>;
using Count = std::uint64_t;

constexpr std::array<Twelve, 6> triangulations = {{
    {1,0,3,2,6,9,4,10,11,5,7,8}, {3,4,5,0,1,2,9,10,11,6,7,8},
    {3,4,6,0,1,9,2,10,11,5,7,8}, {3,4,6,0,1,9,2,11,10,5,8,7},
    {3,6,9,0,7,10,1,4,11,2,5,8}, {3,6,9,0,7,11,1,4,10,2,8,5}
}};

// A port is a side of a complementary polygon on the cut surface.
// The polygon sides are numbered consecutively in their boundary order.
struct Scheme {
    int ports = 0;
    Twelve other{}, vertex{}, band{};
    int bands = 0;

    void number_bands() {
        bands = 0;
        for (int p = 0; p < ports; ++p) {
            if (p < other[p]) {
                band[p] = band[other[p]] = bands++;
            }
        }
    }

    Count key() const {
        Count end_of_polygon = 0;
        for (int p = 0; p < ports; ++p) {
            if (p+1 == ports || vertex[p] != vertex[p+1]) end_of_polygon |= Count(1) << p;
        }
        Count k = end_of_polygon;
        for (int p = 0; p < 12; ++p) k = (k << 4) | (p < ports ? other[p] : 15);
        return k;
    }
};

struct Circuit {
    unsigned mask;  // Real bands crossed exactly once.
    List exits;     // Polygon ports in traversal order.
};

class Circuits {
    std::unordered_map<Count, std::vector<Circuit>> cache;

    static void join(const Scheme &s, unsigned mask, Twelve &chord, std::vector<Circuit> &out) {
        int a = 0;
        while (a < s.ports && chord[a] != -1) ++a;
        if (a == s.ports) {
            int start = 0;
            while (chord[start] < 0) ++start;
            List exits;
            unsigned used = 0;
            int p = start;
            do {
                exits.push_back(p);
                used |= 1u << s.band[p];
                p = chord[s.other[p]];
            } while (p != start);
            if (used == mask) out.push_back({mask, std::move(exits)});
            return;
        }
        for (int b = a+1; b < s.ports && s.vertex[b] == s.vertex[a]; ++b) {
            if (chord[b] != -1) continue;
            bool crosses = false;
            for (int p = a+1; p < b; ++p) {
                if (chord[p] >= 0 && (chord[p] < a || b < chord[p])) {crosses = true; break;}
            }
            if (crosses) continue;
            chord[a] = b; chord[b] = a;
            join(s, mask, chord, out);
            chord[a] = chord[b] = -1;
        }
    }

public:
    const std::vector<Circuit> &get(const Scheme &s) {
        auto result = cache.try_emplace(s.key());
        auto &circuits = result.first->second;
        if (result.second) {
            for (unsigned mask = 1; mask < (1u << s.bands); ++mask) {
                Twelve chord;
                chord.fill(-2);
                for (int p = 0; p < s.ports; ++p) {
                    if (mask & (1u << s.band[p])) chord[p] = -1;
                }
                join(s, mask, chord, circuits);
            }
        }
        return circuits;
    }
};

int cost(unsigned mask, const Six &width) {
    int total = 0;
    for (int i = 0; i < 6; ++i) if (mask & (1u << i)) total += width[i];
    return total;
}

struct Diagram {
    Scheme scheme;
    Six width{};
    std::array<List, 12> crossing;
    List partner, direction, parallel, number, ports;
    std::vector<unsigned char> seen;

    // The two ends at position j on the first curve are 2j and 2j+1.
    // An arc of the second curve joins a departure to the next arrival.
    // Returns false when the two curves have a common disjoint vertex (or coincide).
    bool fill(const List &word) {
        int n = static_cast<int>(word.size());
        if (!n) return false;
        partner.resize(2*n); direction.resize(2*n);
        for (int j = 0; j < n; ++j) {
            int a = word[j], b = word[(j+1 == n) ? 0 : j+1];
            int tail = 2*(std::abs(a)-1) + (a < 0);
            int head = 2*(std::abs(b)-1) + (b > 0);
            partner[tail] = head; partner[head] = tail;
            direction[tail] = j+1; direction[head] = -(j+1);
        }
        auto advance = [&](int p) {
            int q = partner[p];
            if (q % 2 == 0) return q+2 == 2*n ? 0 : q+2;
            return q == 1 ? 2*n-1 : q-2;
        };
        seen.assign(2*n, 0);
        parallel.assign(2*n, -1);
        number.resize(2*n);
        ports.clear();
        int regions = 0, polygons = 0;
        bool monogon = false;
        for (int a = 0; a < 2*n; ++a) {
            if (seen[a]) continue;
            ++regions;
            int b = advance(a);
            seen[a] = 1;
            if (a == b) {monogon = true; continue;}
            if (advance(b) == a) {
                parallel[a] = b; parallel[b] = a;
                seen[b] = 1;
                continue;
            }
            int p = a;
            do {
                seen[p] = 1;
                int id = static_cast<int>(ports.size());
                number[p] = id;
                if (id < 12) scheme.vertex[id] = polygons;
                ports.push_back(p);
                p = advance(p);
            } while (p != a);
            ++polygons;
        }
        if (regions > n-2) return false;
        if (regions != n-2 || monogon || ports.size() > 12 || ports.empty())
            throw std::runtime_error("unexpected geometry in a filling diagram");
        scheme.ports = static_cast<int>(ports.size());
        for (int i = 0; i < scheme.ports; ++i) {
            auto &strip = crossing[i];
            strip.clear();
            int port = ports[i];
            for (;;) {
                strip.push_back(direction[port]);
                int across = partner[port];
                if (parallel[across] < 0) {
                    scheme.other[i] = number[across];
                    break;
                }
                port = parallel[across];
            }
        }
        scheme.number_bands();
        width.fill(0);
        for (int i = 0; i < scheme.ports; ++i) width[scheme.band[i]] = static_cast<int>(crossing[i].size());
        return true;
    }

    // Each original arc is met at most once. Bucket the signed labels by
    // their positions on the second curve, so its cyclic order is preserved.
    void child(const Circuit &cycle, List &out, List &bucket) const {
        bucket.assign(partner.size()/2, 0);
        int label = 0;
        for (int p : cycle.exits) for (int arc : crossing[p]) {
            ++label;
            bucket[std::abs(arc)-1] = (arc > 0) ? label : -label;
        }
        out.clear();
        for (int v : bucket) if (v) out.push_back(v);
    }
};

struct Level {
    Diagram diagram;
    List child_word, bucket;
    std::vector<std::pair<int,int>> candidates;
};

class ShortPaths {
    std::array<Level,6> levels;
    Circuits &library;
    const std::array<int,7> &threshold;

public:
    ShortPaths(Circuits &bank, const std::array<int,7> &lower) : library(bank), threshold(lower) {}

    bool found(const List &word, int budget) {
        if (static_cast<int>(word.size()) < threshold[budget+1]) return true;
        auto &level = levels[budget];
        auto &diagram = level.diagram;
        if (!diagram.fill(word)) return true;
        if (budget == 2) return false;
        const auto &cycles = library.get(diagram.scheme);
        level.candidates.clear();
        for (int i = 0; i < static_cast<int>(cycles.size()); ++i) {
            int crossings = cost(cycles[i].mask, diagram.width);
            if (crossings < threshold[budget]) return true;
            level.candidates.emplace_back(crossings, i);
        }
        std::sort(level.candidates.begin(),level.candidates.end());
        for (auto [crossings, i] : level.candidates) {
            diagram.child(cycles[i], level.child_word, level.bucket);
            if (found(level.child_word,budget-1)) return true;
        }
        return false;
    }
};

struct Chart {
    Scheme scheme;
    std::array<List,2> circles;
    Six balance{}, order{};
    std::vector<unsigned> masks;

    Chart(const Twelve &mate, Circuits &bank) {
        scheme.ports = 12; scheme.other = mate;
        for (int i = 0; i < 12; ++i) scheme.vertex[i] = i/3;
        scheme.number_bands();
        std::array<bool,12> used{};
        int component = 0;
        for (int start = 0; start < 12; ++start) if (!used[start]) {
            if (component == 2) throw std::runtime_error("too many boundaries");
            auto &circle = circles[component++];
            int p = start;
            do {
                used[p] = true; circle.push_back(p);
                int q = mate[p]; p = 3*(q/3) + (q+1)%3;
            } while (p != start);
        }
        if (component != 2) throw std::runtime_error("wrong boundary count");
        balance.fill(-1);
        for (auto p : circles[0]) ++balance[scheme.band[p]];
        for (const auto &r : bank.get(scheme)) masks.push_back(r.mask);
        std::sort(masks.begin(),masks.end());
        masks.erase(std::unique(masks.begin(),masks.end()),masks.end());
        // Reserve two different balance coefficients, so the last two widths
        // are uniquely determined by total width and boundary balance.
        int lo = std::min_element(balance.begin(),balance.end())-balance.begin();
        int hi = std::max_element(balance.begin(),balance.end())-balance.begin();
        if (lo == hi) throw std::runtime_error("no distinct balance coefficients");
        int j = 0;
        for (int e = 0; e < 6; ++e) if(e!=lo && e!=hi) order[j++] = e;
        order[4] = lo; order[5] = hi;
    }
};

class Gluings {
    const Chart &chart;
    int n;
    List partner;
    std::array<int,12> first{};
public:
    Gluings(const Chart &c, int count) : chart(c), n(count), partner(2*count) {}

    void set_widths(const Six &width) {
        std::array<int,12> increment{};
        for (int side = 0; side < 2; ++side) {
            int offset = 0;
            for (int port : chart.circles[side]) {
                first[port] = side == 0 ? 2*offset : 2*(n-1-offset)+1;
                increment[port] = side == 0 ? 2 : -2;
                offset += width[chart.scheme.band[port]];
            }
            if (offset != n) throw std::runtime_error("boundary balance failed");
        }
        for (int p = 0; p < 12; ++p) {
            int q = chart.scheme.other[p];
            if (p > q) continue;
            int weight = width[chart.scheme.band[p]];
            int a = first[p], b = first[q]+(weight-1)*increment[q];
            for (int k = 0; k < weight; ++k, a+=increment[p], b-=increment[q]) {
                partner[a] = b; partner[b] = a;
            }
        }
    }

    // The arc pairing stays fixed. The shift only changes the map that joins
    // an arrival at one boundary to the corresponding departure at the other.
    bool read(int shift, List &word, List &transposed) const {
        int d = 0;
        word.clear();
        do {
            int j = d/2;
            if (d % 2) {
                j -= shift;
                if (j < 0) j += n;
                word.push_back(-j-1);
                transposed[j] = -static_cast<int>(word.size());
            } else {
                word.push_back(j+1);
                transposed[j] = static_cast<int>(word.size());
            }
            int a = partner[d];
            if (a % 2) {
                int k = a/2-shift;
                d = 2*(k < 0 ? k+n : k);
            } else {
                int k = a/2+shift;
                d = 2*(k >= n ? k-n : k)+1;
            }
        } while (d != 0);
        return static_cast<int>(word.size()) == n;
    }
};

struct Counts {Count widths=0, shifts=0, connected=0, rejected=0, survivors=0;};

class CheckSize {
    const Chart &chart;
    ShortPaths &paths;
    int n, distance, cutoff, chart_number;
    Gluings gluing;
    Counts &counts;
    Six width{};
    List word, inverse;
    bool stop_first, stopped = false;

    void check_widths() {
        for (unsigned mask : chart.masks) if (cost(mask,width) < cutoff) return;
        ++counts.widths;
        gluing.set_widths(width);
        for (int shift = 0; shift < n; ++shift) {
            ++counts.shifts;
            if (!gluing.read(shift,word,inverse)) continue;
            ++counts.connected;
            if (paths.found(inverse,distance-1) || paths.found(word,distance-1)) {
                ++counts.rejected;
                continue;
            }
            ++counts.survivors;
            std::cout << "SURVIVOR " << distance << ' ' << n << " chart " << chart_number << " widths";
            for (auto x : width) std::cout << ' ' << x;
            std::cout << " shift " << shift << " word";
            for (auto x : word) std::cout << ' ' << x;
            std::cout << std::endl;
            if (stop_first) {stopped=true;return;}
        }
    }

    void extend(int level, int left, int imbalance) {
        if (stopped) return;
        if (level == 4) {
            int i=chart.order[4], j=chart.order[5];
            int numerator = imbalance+chart.balance[j]*left;
            int denominator = chart.balance[j]-chart.balance[i];
            if (numerator<0 || numerator%denominator!=0) return;
            int a=numerator/denominator;
            if (a>left) return;
            width[i]=a; width[j]=left-a;
            check_widths();
            return;
        }
        int i=chart.order[level];
        for (int a=0; a<=left && !stopped; ++a) {
            width[i]=a;
            extend(level+1,left-a,imbalance+chart.balance[i]*a);
        }
    }

public:
    CheckSize(const Chart &c, ShortPaths &finder, int size, int d, int minimum,
              int type, Counts &sum, bool first) :
        chart(c), paths(finder), n(size), distance(d), cutoff(minimum), chart_number(type),
        gluing(c,size), counts(sum), inverse(size), stop_first(first) {}
    bool run() {extend(0,n,0);return stopped;}
};

int main(int argc, char **argv) {
    try {
        if (argc<4 || argc>5) throw std::runtime_error("usage: certify_lower DISTANCE FIRST LAST [first|all]");
        int d=std::stoi(argv[1]), lo=std::stoi(argv[2]), hi=std::stoi(argv[3]);
        if (d<4 || d>6 || lo<1 || hi<lo) throw std::runtime_error("expected distance 4..6 and positive sizes");
        bool first=argc==4 || std::string(argv[4])=="first";
        if (argc==5 && !first && std::string(argv[4])!="all") throw std::runtime_error("expected first or all");
        // Only established strictly lower distances may be used in this run.
        std::array<int,7> threshold{};
        threshold[3]=4;
        if (d>=5) threshold[4]=12;
        if (d>=6) threshold[5]=40;
        Circuits bank;
        ShortPaths paths(bank,threshold);
        std::vector<Chart> charts;
        for (const auto &m : triangulations) charts.emplace_back(m,bank);
        for (int n=lo; n<=hi; ++n) {
            Counts counts;
            bool stopped=false;
            for (int i=0; i<static_cast<int>(charts.size()) && !stopped; ++i) {
                CheckSize check(charts[i],paths,n,d,threshold[d-1],i,counts,first);
                stopped=check.run();
            }
            std::cout << "ROW " << d << ' ' << n << " widths " << counts.widths << " shifts " << counts.shifts
                << " connected " << counts.connected << " rejected " << counts.rejected
                << " survivors " << counts.survivors << " complete " << !stopped << std::endl;
            if (stopped) break;
        }
    } catch (const std::exception &e) {std::cerr << e.what()<<std::endl;return 1;}
}
