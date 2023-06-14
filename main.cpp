#include <algorithm>
#include <math.h>
#include <string>
#include <vector>
#include <queue>
#include <map>
#include <unordered_map>
#include <iostream>

#include "raylib.h"

// --- data structures

#define INF 1000

struct Vertex;
struct Edge;
struct Graph;

typedef int VertexId;
typedef std::vector<Vertex> VertList;
typedef std::vector<Edge> EdgeList;

std::string G_log;

struct Vertex
{
    Vector2 position;
    bool visited;
    float radius = 40;
    int reachCost = INF;
};

struct Edge
{
    enum Type
    {
        NIL,   // generic edge
        DISC,  // edge which connects to an unvisited node
        BACK,  // edge which connects to a visited node (DFS)
        CROSS, // edge which connects to a visited node (BFS)
        TREE   // edge which is part of the MST
    };

    VertexId a;
    VertexId b;
    int weight;
    Type type = Type::NIL;
};

struct Graph
{
    VertList V;
    EdgeList E;
    bool isDirected = false; // if true, edges are to be interpreted as (a -> b)
};

template <typename T>
struct UnionFind
{
    std::unordered_map<T, T> parent;
    std::unordered_map<T, int> dist;

    void init(const std::vector<T> &vec)
    {
        for (auto &&v : vec)
        {
            parent[v] = v;
            dist[v] = 1;
        }
    }

    T find(const T &val)
    {
        if (parent[val] == val)
            return val;

        return find(parent[val]);
    }

    void unify(const T &a, const T &b)
    {
        T x = find(a);
        T y = find(b);

        if (x == y)
            return;

        if (dist[x] <= dist[y])
            std::swap(x, y);

        parent[y] = x;
        dist[x] += dist[y];
    }
};

// --- utils

void resetGraph(Graph &G)
{
    for (auto &&v : G.V)
    {
        v.visited = false;
        v.reachCost = INF;
    }

    for (auto &&e : G.E)
        e.type = Edge::Type::NIL;
}

float distance(const Vector2 &a, const Vector2 &b)
{
    float xDiff = a.x - b.x;
    float yDiff = a.y - b.y;
    return std::sqrt((xDiff * xDiff) + (yDiff * yDiff));
}

Vector2 middlePoint(const Vector2 &v1, const Vector2 &v2)
{
    return {(v1.x + v2.x) / 2, (v1.y + v2.y) / 2};
}

bool isIncident(const Edge &e, const VertexId &vid)
{
    return e.a == vid || e.b == vid;
}

// --- graph traversal

void dfsTraversal(Graph &G, VertexId source)
{
    VertList &Lv = G.V;
    EdgeList &Le = G.E;
    Lv[source].visited = true;

    for (auto &&e : Le)
    {
        if (e.type == Edge::Type::NIL && isIncident(e, source))
        {
            auto opposite = e.a == source ? e.b : e.a;
            if (Lv[opposite].visited)
                e.type = Edge::Type::BACK;
            else
            {
                e.type = Edge::Type::DISC;
                dfsTraversal(G, opposite);
            }
        };
    }
}

void bfsTraversal(Graph &G, VertexId source)
{
    VertList &Lv = G.V;
    EdgeList &Le = G.E;
    Lv[source].visited = true;

    std::vector<std::vector<VertexId>> layers{{source}};
    unsigned int i = 0;

    while (!layers[i].empty())
    {
        layers.push_back({});

        for (auto &&v : layers[i])
        {
            for (auto &&e : Le)
            {
                if (e.type == Edge::Type::NIL && isIncident(e, v))
                {
                    const auto opposite = e.a == v ? e.b : e.a;
                    if (Lv[opposite].visited)
                        e.type = Edge::Type::CROSS;
                    else
                    {
                        e.type = Edge::Type::DISC;
                        Lv[opposite].visited = true;
                        layers[i + 1].push_back(opposite);
                    }
                }
            }
        }
        i++;
    }
}

// --- mst - minimum spanning tree

void mstHeapPrim(Graph &G, VertexId source)
{
    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;

    std::map<VertexId, VertexId> parents;
    std::vector<VertexId> heap;

    for (unsigned int i = 0; i < Lv.size(); i++)
    {
        parents[i] = -1;
        heap.push_back(i);
    }

    Lv[source].reachCost = 0;

    while (!heap.empty())
    {
        std::sort(
            heap.begin(),
            heap.end(),
            [&Lv](auto a, auto b)
            { return Lv[a].reachCost >= Lv[b].reachCost; });

        const auto min = heap.back();
        heap.pop_back();

        for (auto &&e : Le)
        {
            if (isIncident(e, min))
            {
                const auto opposite = e.a == min ? e.b : e.a;
                if (std::find(heap.begin(), heap.end(), opposite) != heap.end())
                {
                    Lv[opposite].reachCost = std::min(e.weight, Lv[opposite].reachCost);
                    parents[opposite] = min;
                }
            }
        }
    }

    for (auto &&v : parents)
        if (v.second != -1)
            for (auto &&e : Le)
                if ((e.a == v.first && e.b == v.second) || (e.a == v.second && e.b == v.first))
                    e.type = Edge::Type::TREE;
}

void mstUnionFindKruskal(Graph &G)
{
    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;

    std::vector<VertexId> vids(Lv.size());
    for (unsigned int i = 0; i < Lv.size(); i++)
        vids.push_back(i);

    UnionFind<VertexId> uf;
    uf.init(vids);

    std::sort(
        G.E.begin(),
        G.E.end(),
        [](auto e1, auto e2)
        { return e1.weight <= e2.weight; });

    for (auto &&e : G.E)
    {
        if (uf.find(e.a) != uf.find(e.b))
        {
            e.type = Edge::Type::TREE;
            uf.unify(e.a, e.b);
        }
    }
}

// --- sssp - single source shortest path

void ssspHeapDijkstra(Graph &G, VertexId source)
{
    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;
    std::vector<VertexId> heap;

    for (unsigned int i = 0; i < Lv.size(); i++)
        heap.push_back(i);

    Lv[source].reachCost = 0;

    while (!heap.empty())
    {
        std::sort(
            heap.begin(),
            heap.end(),
            [&Lv](auto a, auto b)
            { return Lv[a].reachCost >= Lv[b].reachCost; });

        const auto min = heap.back();
        heap.pop_back();

        for (auto &&e : Le)
        {
            if (isIncident(e, min))
            {
                const auto opposite = e.a == min ? e.b : e.a;
                Lv[opposite].reachCost = std::min(Lv[opposite].reachCost, e.weight + Lv[min].reachCost);
            }
        }
    }
}

void ssspBellmanFord(Graph &G, VertexId source)
{
    if (!G.isDirected)
    {
        G_log = "ssspBellmanFord: undirected graphs are not supported";
        return;
    }

    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;
    bool cycle = false;
    Lv[source].reachCost = 0;

    for (unsigned int i = 0; i < Lv.size() - 1; i++)
        for (auto &&e : Le)
            if (Lv[e.a].reachCost != INF)
                Lv[e.b].reachCost = std::min(Lv[e.b].reachCost, Lv[e.a].reachCost + e.weight);

    for (auto &&e : Le)
        if (Lv[e.a].reachCost != INF && Lv[e.b].reachCost > Lv[e.a].reachCost + e.weight)
        {
            G_log = "ssspBellmanFord: a negative cycle was found";
            break;
        }
}

// --- apsp - all pairs shortest path

void apspDpBellmanFord(Graph &G, VertexId source)
{
}

void apspDpFloydWarshall(Graph &G)
{
    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;

    int costs[Lv.size()][Lv.size()];
    for (unsigned int i = 0; i < Lv.size(); i++)
        for (unsigned int j = 0; j < Lv.size(); j++)
            costs[i][j] = INF;

    for (unsigned int i = 0; i < Lv.size(); i++)
        costs[i][i] = 0;

    for (auto &&e : Le)
        costs[e.a][e.b] = e.weight;

    for (unsigned int i = 0; i < Lv.size(); i++)
        for (unsigned int a = 0; a < Lv.size(); a++)
            for (unsigned int b = 0; b < Lv.size(); b++)
                costs[a][b] = std::min(costs[a][b], costs[a][i] + costs[i][b]);

    for (unsigned int i = 0; i < Lv.size(); i++)
        if (costs[i][i])
        {
            G_log = "apspDpFloydWarshall: a negative cycle was found";
            break;
        }

    // debug
    for (unsigned int i = 0; i < Lv.size(); i++)
    {
        for (unsigned int j = 0; j < Lv.size(); j++)
            std::cout << costs[i][j] << " - ";
        std::cout << "\n";
    }
}

// --- visualization

void drawLog()
{
    DrawText(G_log.c_str(), 10, 10, 25, DARKPURPLE);
}

void drawVertex(const Vertex &v)
{
    const auto vertColor = v.visited ? BLUE : BLACK;
    DrawCircleV(v.position, v.radius, vertColor);
    DrawRing(v.position, v.radius, v.radius + 1, 360, 0, 0, WHITE);
}

void drawEdge(const VertList &Lv, const Edge &e, bool isDirected)
{
    auto edgeColor = BLACK;
    switch (e.type)
    {
    case Edge::Type::NIL:
        edgeColor = BLACK;
        break;
    case Edge::Type::DISC:
        edgeColor = GREEN;
        break;
    case Edge::Type::BACK:
        edgeColor = RED;
        break;
    case Edge::Type::CROSS:
        edgeColor = RED;
        break;
    case Edge::Type::TREE:
        edgeColor = GREEN;
        break;
    }
    DrawLineEx(
        Lv[e.a].position,
        Lv[e.b].position,
        std::abs(e.weight),
        edgeColor);

    if (isDirected)
    {
        DrawLineEx(
            middlePoint(middlePoint(Lv[e.a].position, Lv[e.b].position), Lv[e.b].position),
            Lv[e.b].position,
            std::abs(e.weight) * 2,
            RED);
    }
}

void drawEdgeWeights(const VertList &Lv, const Edge &e)
{
    const auto fontSize = 20.0f;
    const auto edgeWeight = std::to_string(e.weight);
    const auto weightPos = middlePoint(Lv[e.a].position, Lv[e.b].position);

    DrawRectangle(weightPos.x, weightPos.y, fontSize * 2, fontSize * 2, BLACK);
    DrawText(
        edgeWeight.c_str(),
        weightPos.x + fontSize / 2,
        weightPos.y + fontSize / 2,
        fontSize, WHITE);
}

void drawVertexNames(const Vertex &v, int vid)
{
    const auto fontSize = 20;
    const auto vertName = "id: " + std::to_string(vid);
    DrawText(
        vertName.c_str(),
        v.position.x - fontSize,
        v.position.y - fontSize / 2,
        fontSize, WHITE);
}

void drawVertexReachCosts(const Vertex &v)
{
    const auto fontSize = 16.0f;
    const auto labelSize = 50.0f;
    const std::string vertReachCost = v.reachCost == INF ? "INF" : std::to_string(v.reachCost);

    DrawRectangle(
        v.position.x + fontSize,
        v.position.y + fontSize,
        labelSize,
        labelSize,
        BLACK);

    DrawRectangleLines(
        v.position.x + fontSize,
        v.position.y + fontSize,
        labelSize,
        labelSize,
        WHITE);

    DrawText(
        vertReachCost.c_str(),
        v.position.x + fontSize * 2,
        v.position.y + fontSize * 2,
        fontSize, RED);
}

void drawGraph(const Graph &G)
{
    for (auto &&e : G.E)
    {
        drawEdge(G.V, e, G.isDirected);
        drawEdgeWeights(G.V, e);
    }

    for (unsigned int i = 0; i < G.V.size(); i++)
    {
        drawVertex(G.V[i]);
        drawVertexNames(G.V[i], i);
        drawVertexReachCosts(G.V[i]);
    }
}

void highlightSourceAndDestination(const Vertex &source, const Vertex &destination)
{
    if (&source == &destination)
    {
        DrawRing(source.position, source.radius, source.radius + 10, -180, 0, 0, YELLOW);
        DrawRing(source.position, source.radius, source.radius + 10, +180, 0, 0, BROWN);
        return;
    }

    DrawRing(source.position, source.radius, source.radius + 10, 360, 0, 0, YELLOW);
    DrawRing(destination.position, destination.radius, destination.radius + 10, 360, 0, 0, BROWN);
}

VertexId vertexAtCoord(const VertList &Lv, const Vector2 &mousePos)
{
    for (unsigned int i = 0; i < Lv.size(); i++)
        if (distance(Lv[i].position, mousePos) <= Lv[i].radius)
            return i;
    return -1;
}

void handleDragVertex(VertList &Lv)
{
    if (IsMouseButtonDown(MOUSE_BUTTON_LEFT))
    {
        const auto mousePos = GetMousePosition();
        const auto selectedVert = vertexAtCoord(Lv, mousePos);
        if (selectedVert == -1)
            return;

        Lv[selectedVert].position = mousePos;
    }
}

void handleSelectSourceAndDestination(VertList &Lv, VertexId &source, VertexId &destination)
{
    if (IsMouseButtonDown(MOUSE_BUTTON_RIGHT))
    {
        const auto selectedVert = vertexAtCoord(Lv, GetMousePosition());
        if (selectedVert == -1)
            return;

        if (IsKeyDown(KEY_LEFT_SHIFT))
            destination = selectedVert;
        else
            source = selectedVert;
    }
}

void randomizeVertexPositions(VertList &Lv, int screen_w, int screen_h)
{
    for (auto &&v : Lv)
        v.position = {
            static_cast<float>(rand() % screen_w),
            static_cast<float>(rand() % screen_h)};
}

int main()
{
    int screen_w = 900;
    int screen_h = 800;

    InitWindow(screen_w, screen_h, "Graph algos");
    SetWindowState(FLAG_WINDOW_RESIZABLE);
    SetTargetFPS(60);

    VertList Lv(7);
    EdgeList Le{
        {0, 1, 2},
        {0, 2, -1},
        {1, 3, 2},
        {2, 4, -3},
        {3, 4, 1},
        {3, 5, 5},
        {4, 5, 20},
        {4, 6, -2}};

    Graph G{Lv, Le};
    VertexId source = rand() % Lv.size();
    VertexId destination = rand() % Lv.size();
    randomizeVertexPositions(G.V, screen_w, screen_h);

    while (!WindowShouldClose())
    {
        BeginDrawing();
        ClearBackground({200, 200, 244});
        {
            handleDragVertex(G.V);
            handleSelectSourceAndDestination(G.V, source, destination);

            if (IsKeyPressed(KEY_ENTER))
                G.isDirected = !G.isDirected;

            if (IsKeyPressed(KEY_D))
                dfsTraversal(G, source);

            if (IsKeyPressed(KEY_B))
                bfsTraversal(G, source);

            if (IsKeyPressed(KEY_P))
                mstHeapPrim(G, source);

            if (IsKeyPressed(KEY_K))
                mstUnionFindKruskal(G);

            if (IsKeyPressed(KEY_J))
                ssspHeapDijkstra(G, source);

            if (IsKeyPressed(KEY_F))
                ssspBellmanFord(G, source);

            if (IsKeyPressed(KEY_W))
                apspDpFloydWarshall(G);

            if (IsKeyPressed(KEY_R))
                randomizeVertexPositions(G.V, screen_w, screen_h);

            if (IsKeyPressed(KEY_BACKSPACE))
            {
                resetGraph(G);
                G_log = "";
            }

            highlightSourceAndDestination(G.V[source], G.V[destination]);
            drawGraph(G);
            drawLog();
        }
        EndDrawing();
    }
    CloseWindow();
    return 0;
}