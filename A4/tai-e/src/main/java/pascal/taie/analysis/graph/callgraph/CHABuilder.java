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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod m = workList.poll();
            if (!callGraph.contains(m)){
                callGraph.addReachableMethod(m);
                for (Invoke callSite : callGraph.callSitesIn(m).toList()){
                    Set<JMethod> T = resolve(callSite);
                    for (JMethod m1 : T){
                        if (m1 != null){
                            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, m1));
                            workList.add(m1);
                        }
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature s =  methodRef.getSubsignature();
        JClass c =  methodRef.getDeclaringClass();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
            case SPECIAL:
                JMethod m =  dispatch(c, s);
                T.add(m);
                break;
            case VIRTUAL:
            case INTERFACE: {
                Queue<JClass> subclasses = new ArrayDeque<>();
                Set<JClass> visit = new HashSet<>();
                subclasses.add(c);
                visit.add(c);
                while (!subclasses.isEmpty()) {
                    JClass subclass = subclasses.poll();
                    if (CallGraphs.getCallKind(callSite) == CallKind.INTERFACE){
                        for (JClass jClass :hierarchy.getDirectImplementorsOf(subclass)) {
                            if (!visit.contains(jClass)) {
                                subclasses.add(jClass);
                                visit.add(jClass);
                            }
                        }
                        for (JClass jClass :hierarchy.getDirectSubinterfacesOf(subclass)) {
                            if (!visit.contains(jClass)) {
                                subclasses.add(jClass);
                                visit.add(jClass);
                            }
                        }
                    }
                    else{
                        for (JClass jClass : hierarchy.getDirectSubclassesOf(subclass)) {
                            if (!visit.contains(jClass)) {
                                subclasses.add(jClass);
                                visit.add(jClass);
                            }
                        }
                    }
                    T.add(dispatch(subclass, s));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null)
            return null;
        JMethod m = jclass.getDeclaredMethod(subsignature);
        return (m == null || m.isAbstract()) ? dispatch(jclass.getSuperClass(), subsignature) : m;
    }
}
