/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.awt.*;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // new 语句
            Obj o = heapModel.getObj(stmt);
            VarPtr p = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(p,new PointsToSet(o));
            return null;
        }
        public Void visit(Copy stmt) {
            VarPtr lp = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr rp = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(rp, lp);
            return null;
        }
        public Void visit(LoadArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(StoreArray stmt) {
            return StmtVisitor.super.visit(stmt);
        }
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()){
                VarPtr lp = pointerFlowGraph.getVarPtr(stmt.getLValue());
                StaticField sf = pointerFlowGraph.getStaticField(field);
                addPFGEdge(sf, lp);
            }
            return null;
        }
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()){
                VarPtr rp = pointerFlowGraph.getVarPtr(stmt.getRValue());
                StaticField sf = pointerFlowGraph.getStaticField(field);
                addPFGEdge(rp,sf);
            }
            return null;
        }
        public Void visit(Invoke stmt) {
            if(stmt.getMethodRef().resolve().isStatic()){
                Var lv = stmt.getLValue();
                JMethod m = resolveCallee(null, stmt);
                Edge<Invoke, JMethod> edge = new Edge<>(CallKind.STATIC, stmt, m);
                if(callGraph.addEdge(edge)){
                    addReachable(m);
                    InvokeExp invokeExp = stmt.getInvokeExp();
                    for (int i = 0; i < invokeExp.getArgCount(); i++) {
                        VarPtr ap = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                        VarPtr pp = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));
                        addPFGEdge(ap,pp);
                    }
                    if (lv != null) {
                        for (Var retv : m.getIR().getReturnVars()){
                            VarPtr retp = pointerFlowGraph.getVarPtr(retv);
                            VarPtr lp = pointerFlowGraph.getVarPtr(lv);
                            addPFGEdge(retp, lp);
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (n instanceof VarPtr){
                Var v = ((VarPtr) n).getVar();
                for (Obj o : delta){
                    for (StoreField stmt : v.getStoreFields()){
                        VarPtr rp = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        JField f = stmt.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, f);
                        addPFGEdge(rp, instanceField);
                    }
                    for (LoadField stmt : v.getLoadFields()){
                        VarPtr lp = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        JField f = stmt.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(o, f);
                        addPFGEdge(instanceField, lp);
                    }
                    for (StoreArray stmt : v.getStoreArrays()){
                        VarPtr rp = pointerFlowGraph.getVarPtr(stmt.getRValue());
                        ArrayIndex ai = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(rp, ai);
                    }
                    for (LoadArray stmt : v.getLoadArrays()){
                        VarPtr lp = pointerFlowGraph.getVarPtr(stmt.getLValue());
                        ArrayIndex ai = pointerFlowGraph.getArrayIndex(o);
                        addPFGEdge(ai, lp);
                    }
                    processCall(v, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = new PointsToSet();
        for (Obj o : pointsToSet){
            if (!pointer.getPointsToSet().contains(o)){
                pointer.getPointsToSet().addObject(o);
                delta.addObject(o);
            }
        }
        if (!delta.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach (p -> workList.addEntry(p, delta));
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke stmt : var.getInvokes()){
            JMethod m = resolveCallee(recv, stmt);
            VarPtr thisp = pointerFlowGraph.getVarPtr(m.getIR().getThis());
            workList.addEntry(thisp, new PointsToSet(recv));
            Edge<Invoke, JMethod> edge;
            if (stmt.isDynamic())
                edge = new Edge<>(CallKind.DYNAMIC, stmt, m);
            else if (stmt.isInterface())
                edge = new Edge<>(CallKind.INTERFACE, stmt, m);
            else if (stmt.isSpecial())
                edge = new Edge<>(CallKind.SPECIAL, stmt, m);
            else if (stmt.isVirtual())
                edge = new Edge<>(CallKind.VIRTUAL, stmt, m);
            else
                edge = new Edge<>(CallKind.OTHER, stmt, m);
            if (callGraph.addEdge(edge)){
                addReachable(m);
                for (int i = 0; i < m.getParamCount(); ++i){
                    VarPtr ap = pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i));
                    VarPtr pp = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));
                    addPFGEdge(ap, pp);
                }
                Var lv = stmt.getLValue();
                if (lv != null){
                    for (Var retv : m.getIR().getReturnVars()){
                        VarPtr retp = pointerFlowGraph.getVarPtr(retv);
                        VarPtr lp = pointerFlowGraph.getVarPtr(lv);
                        addPFGEdge(retp, lp);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
