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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.Objects;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpfact = new CPFact();
        for (Var params : cfg.getIR().getParams()) {
            if (canHoldInt(params)){
                cpfact.update(params, Value.getNAC());
            }
        }
        return cpfact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()){
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            target.update(var, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        else if (v1.isUndef()) {
            return v2;
        }
        else if (v2.isUndef()) {
            return v1;
        }
        else if (v1.getConstant() == v2.getConstant()) {
            return v1;
        }
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact in_new = in.copy();
        if (stmt instanceof DefinitionStmt) {
            if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var && canHoldInt((Var)stmt.getDef().get())){
                in_new.update((Var)stmt.getDef().get(), Objects.requireNonNull(evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in_new)));
            }
        }
        return out.copyFrom(in_new);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var){
            return in.get((Var) exp);
        }
        else if (exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if (exp instanceof BinaryExp){
            Var o1 = ((BinaryExp) exp).getOperand1();
            Var o2 = ((BinaryExp) exp).getOperand2();
            Value v1 = in.get(o1);
            Value v2 = in.get(o2);
            if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }
            else if (v1.isNAC() || v2.isNAC()) {
                if (v1.isNAC() && exp instanceof ArithmeticExp &&
                        (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM)) {
                    return Value.getUndef();
                }
                return Value.getNAC();
            }

            if (exp instanceof ArithmeticExp) {
                return switch (((ArithmeticExp) exp).getOperator()) {
                    case ADD -> Value.makeConstant(v1.getConstant() + v2.getConstant());
                    case SUB -> Value.makeConstant(v1.getConstant() - v2.getConstant());
                    case MUL -> Value.makeConstant(v1.getConstant() * v2.getConstant());
                    case DIV -> Value.makeConstant(v1.getConstant() / v2.getConstant());
                    case REM -> Value.makeConstant(v1.getConstant() % v2.getConstant());
                };
            }
            else if (exp instanceof ConditionExp) {
                return switch (((ConditionExp) exp).getOperator()) {
                    case EQ -> Value.makeConstant(v1.getConstant() == v2.getConstant() ? 1 : 0);
                    case NE -> Value.makeConstant(v1.getConstant() != v2.getConstant() ? 1 : 0);
                    case LT -> Value.makeConstant(v1.getConstant() < v2.getConstant() ? 1 : 0);
                    case GT -> Value.makeConstant(v1.getConstant() > v2.getConstant() ? 1 : 0);
                    case LE -> Value.makeConstant(v1.getConstant() <= v2.getConstant() ? 1 : 0);
                    case GE -> Value.makeConstant(v1.getConstant() >= v2.getConstant() ? 1 : 0);
                };
            }
            else if  (exp instanceof BitwiseExp) {
                return switch (((BitwiseExp) exp).getOperator()) {
                    case OR -> Value.makeConstant(v1.getConstant() | v2.getConstant());
                    case AND -> Value.makeConstant(v1.getConstant() & v2.getConstant());
                    case XOR -> Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                };
            }
            else if  (exp instanceof ShiftExp) {
                return switch (((ShiftExp) exp).getOperator()) {
                    case SHL -> Value.makeConstant(v1.getConstant() << v2.getConstant());
                    case SHR -> Value.makeConstant(v1.getConstant() >> v2.getConstant());
                    case USHR -> Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                };
            }
        }
        return Value.getNAC();
    }
}
