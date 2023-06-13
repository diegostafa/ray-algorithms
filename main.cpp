#include <algorithm>
#include <math.h>
#include <string>
#include <vector>
#include <queue>
#include <map>
#include <unordered_map>
#include <iostream>

#include "raylib.h"

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

enum EdgeType
{
    NIL,   // generic edge
    DISC,  // edge which connects to an unvisited node
    BACK,  // edge which connects to a visited node (DFS)
    CROSS, // edge which connects to a visited node (BFS)
    TREE   // edge which is part of the MST
};

struct Vertex
{
    Vector2 position;
    bool visited;
    float radius = 40;
};

typedef int VertexId;

struct Edge
{
    VertexId a;
    VertexId b;
    EdgeType type;
    int weight = 5.0f;
};

typedef std::vector<Vertex> VertList;
typedef std::vector<Edge> EdgeList;

struct Graph
{
    VertList V;
    EdgeList E;
};

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

void drawVertex(const Vertex &v)
{
    auto vertColor = v.visited ? BLUE : BLACK;
    DrawCircleV(v.position, v.radius, vertColor);
}

void drawEdge(const VertList &Lv, const Edge &e)
{
    auto edgeColor = BLACK;
    switch (e.type)
    {
    case EdgeType::NIL:
        edgeColor = BLACK;
        break;
    case EdgeType::DISC:
        edgeColor = GREEN;
        break;
    case EdgeType::BACK:
        edgeColor = RED;
        break;
    case EdgeType::CROSS:
        edgeColor = RED;
        break;
    case EdgeType::TREE:
        edgeColor = GREEN;
        break;
    }

    DrawLineEx(Lv[e.a].position, Lv[e.b].position, e.weight, edgeColor);
}

void drawEdgeWeights(const VertList &Lv, const Edge &e)
{
    float fontSize = 20;
    auto edgeWeight = std::to_string(e.weight);
    auto weightPosX = ((Lv[e.a].position.x + Lv[e.b].position.x) / 2);
    auto weightPosY = ((Lv[e.a].position.y + Lv[e.b].position.y) / 2);

    DrawRectangle(weightPosX, weightPosY, fontSize * 2, fontSize * 2, BLACK);
    DrawText(
        edgeWeight.c_str(),
        weightPosX + fontSize / 2,
        weightPosY + fontSize / 2,
        fontSize, WHITE);
}

void drawVertexNames(const Vertex &v, int vid)
{
    float fontSize = 20;
    auto vertName = std::to_string(vid);
    DrawText(
        vertName.c_str(),
        v.position.x - fontSize / 2,
        v.position.y - fontSize / 2,
        fontSize, WHITE);
}

void drawGraph(const Graph &G)
{
    for (auto &&e : G.E)
    {
        drawEdge(G.V, e);
        drawEdgeWeights(G.V, e);
    }

    for (unsigned int i = 0; i < G.V.size(); i++)
    {
        drawVertex(G.V[i]);
        drawVertexNames(G.V[i], i);
    }
}

void resetGraph(Graph &G)
{
    for (auto &&v : G.V)
        v.visited = false;

    for (auto &&e : G.E)
        e.type = EdgeType::NIL;
}

float distance(const Vector2 &a, const Vector2 &b)
{
    float xDiff = a.x - b.x;
    float yDiff = a.y - b.y;
    return std::sqrt((xDiff * xDiff) + (yDiff * yDiff));
}

bool isIncident(const Edge &e, const VertexId &vid)
{
    return e.a == vid || e.b == vid;
}

void dfsTraversal(Graph &G, VertexId source)
{
    VertList &Lv = G.V;
    EdgeList &Le = G.E;
    Lv[source].visited = true;

    for (auto &&e : Le)
    {
        if (e.type == EdgeType::NIL && isIncident(e, source))
        {
            auto opposite = e.a == source ? e.b : e.a;
            if (Lv[opposite].visited)
                e.type = EdgeType::BACK;
            else
            {
                e.type = EdgeType::DISC;
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
                if (e.type == EdgeType::NIL && isIncident(e, v))
                {
                    auto opposite = e.a == v ? e.b : e.a;
                    if (Lv[opposite].visited)
                        e.type = EdgeType::CROSS;
                    else
                    {
                        e.type = EdgeType::DISC;
                        Lv[opposite].visited = true;
                        layers[i + 1].push_back(opposite);
                    }
                }
            }
        }
        i++;
    }
}

void mstHeapPrim(Graph &G, VertexId source)
{
    std::vector<Vertex> &Lv = G.V;
    std::vector<Edge> &Le = G.E;

    std::map<VertexId, int> costs{};
    std::map<VertexId, VertexId> parents{};
    std::vector<VertexId> heap;

    for (unsigned int i = 0; i < G.V.size(); i++)
    {
        costs[i] = __INT_MAX__;
        parents[i] = -1;
        heap.push_back(i);
    }
    costs[source] = 0;

    while (!heap.empty())
    {
        std::sort(heap.begin(), heap.end(), [&costs](auto a, auto b)
                  { return costs[a] >= costs[b]; });

        auto min = heap.back();
        heap.pop_back();

        for (auto &&e : Le)
        {
            if (isIncident(e, min))
            {
                auto opposite = e.a == min ? e.b : e.a;
                if (std::find(heap.begin(), heap.end(), opposite) != heap.end() &&
                    e.weight < costs[opposite])
                {
                    costs[opposite] = e.weight;
                    parents[opposite] = min;
                }
            }
        }
    }

    for (auto &&v : parents)
        if (v.second != -1)
            for (auto &&e : Le)
                if ((e.a == v.first && e.b == v.second) || (e.a == v.second && e.b == v.first))
                    e.type = EdgeType::TREE;
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
            e.type = EdgeType::TREE;
            uf.unify(e.a, e.b);
        }
    }
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
        auto mousePos = GetMousePosition();
        auto selectedVert = vertexAtCoord(Lv, mousePos);
        if (selectedVert == -1)
            return;

        Lv[selectedVert].position = mousePos;
    }
}

void handleSelectSourceAndDestination(VertList &Lv, VertexId &source, VertexId &destination)
{
    if (IsMouseButtonDown(MOUSE_BUTTON_RIGHT))
    {
        auto selectedVert = vertexAtCoord(Lv, GetMousePosition());
        if (selectedVert == -1)
            return;

        if (IsKeyDown(KEY_LEFT_SHIFT))
            destination = selectedVert;
        else
            source = selectedVert;
    }
}

int main()
{
    InitWindow(800, 600, "Graph Algos");
    SetTargetFPS(60);

    VertList Lv{
        {{100, 100}, false},
        {{300, 100}, false},
        {{500, 100}, false},
        {{300, 300}, false},
        {{400, 500}, false},
        {{500, 500}, false},
        {{500, 300}, false}};

    EdgeList Le{
        {0, 1, EdgeType::NIL, (rand() % 20) + 5},
        {0, 2, EdgeType::NIL, (rand() % 20) + 5},
        {1, 3, EdgeType::NIL, (rand() % 20) + 5},
        {2, 4, EdgeType::NIL, (rand() % 20) + 5},
        {3, 4, EdgeType::NIL, (rand() % 20) + 5},
        {3, 5, EdgeType::NIL, (rand() % 20) + 5},
        {4, 5, EdgeType::NIL, (rand() % 20) + 5},
        {4, 6, EdgeType::NIL, (rand() % 20) + 5}};

    Graph G{Lv, Le};

    VertexId source = 1;
    VertexId destination = Lv.size() - 1;

    while (!WindowShouldClose())
    {
        BeginDrawing();
        ClearBackground({200, 200, 244});
        {
            handleDragVertex(G.V);
            handleSelectSourceAndDestination(G.V, source, destination);

            drawGraph(G);
            highlightSourceAndDestination(G.V[source], G.V[destination]);

            if (IsKeyPressed(KEY_D))
                dfsTraversal(G, source);

            if (IsKeyPressed(KEY_B))
                bfsTraversal(G, source);

            if (IsKeyPressed(KEY_P))
                mstHeapPrim(G, source);

            if (IsKeyPressed(KEY_K))
                mstUnionFindKruskal(G);

            if (IsKeyPressed(KEY_BACKSPACE))
                resetGraph(G);
        }
        EndDrawing();
    }
    CloseWindow();
    return 0;
}