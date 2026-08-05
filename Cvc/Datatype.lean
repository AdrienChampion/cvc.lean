/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Defs

public import Cvc.Untyped.Defs



namespace Cvc.Datatype variable [Ω]

open cvc5 renaming Datatype → Dt, DatatypeDecl → DtD, DatatypeSelector → DtS
open cvc5 renaming DatatypeConstructor → DtC, DatatypeConstructorDecl → DtCD



namespace Constructor.Decl variable (d : Decl)

@[inherit_doc DtCD.addSelector]
def addSelector (name : String) (sort : Srt) : Env Decl :=
  runUnsafe' do d.toUnsafe.addSelector name sort.toUnsafe

@[inherit_doc DtCD.addSelectorSelf]
def addSelectorSelf (name : String) : Env Decl :=
  runUnsafe' do d.toUnsafe.addSelectorSelf name

@[inherit_doc DtCD.addSelectorUnresolved]
def addSelectorUnresolved (name : String) (unresDatatypeName : String) : Env Decl :=
  runUnsafe' do d.toUnsafe.addSelectorUnresolved name unresDatatypeName

end Constructor.Decl



namespace Decl variable (d : Decl)

@[inherit_doc DtD.addConstructor]
def addConstructor (ctor : Constructor.Decl) : Env Decl :=
  runUnsafe' do d.toUnsafe.addConstructor ctor.toUnsafe

@[inherit_doc DtD.getNumConstructors]
def countConstructors : Nat := d.toUnsafe.getNumConstructors

@[inherit_doc DtD.isParametric]
def isParametric : Bool := d.toUnsafe.isParametric

@[inherit_doc DtD.getName]
def getName : Res String := d.toUnsafe.getName

@[inherit_doc DtD.isResolved]
def isResolved : Env Bool := runUnsafe' do d.toUnsafe.isResolved

end Decl



namespace Selector variable (s : Selector)

@[inherit_doc DtS.getName]
def getName : Res String := s.toUnsafe.getName

@[inherit_doc DtS.getTerm]
def getTerm : Env Term := runUnsafe' do s.toUnsafe.getTerm

@[inherit_doc DtS.getUpdaterTerm]
def getUpdaterTerm : Env Term := runUnsafe' do s.toUnsafe.getUpdaterTerm

@[inherit_doc DtS.getCodomainSort]
def getCodomainSort : Env Srt := runUnsafe' do s.toUnsafe.getCodomainSort

end Selector



namespace Constructor variable (c : Constructor)

@[inherit_doc DtC.getName]
def getName : Res String := c.toUnsafe.getName

def getTerm : Env Term := runUnsafe' do c.toUnsafe.getTerm

def getInstantiatedTerm (retSort : Srt) : Env Term :=
  runUnsafe' do c.toUnsafe.getInstantiatedTerm retSort

def getTesterTerm : Env Term :=
  runUnsafe' do c.toUnsafe.getTesterTerm

def countSelectors : Nat := c.getNumSelectors

@[inherit_doc DtC.getSelector]
def getSelector (name : String) : Env Selector :=
  runUnsafe' do c.toUnsafe.getSelector name

@[inherit_doc DtC.getSelectorAt]
def getSelectorAt (idx : Fin c.countSelectors) : Selector := c.toUnsafe.getSelectorAt idx

instance : GetElem Constructor Nat Selector fun c idx => idx < c.countSelectors :=
  inferInstanceAs (GetElem DtC Nat DtS fun c idx => idx < c.getNumSelectors)

instance [Monad m] : ForIn m Constructor Selector := inferInstanceAs (ForIn m DtC DtS)

end Constructor



section variable (dt : Datatype)

@[inherit_doc Dt.getConstructor]
def getConstructor (name : String) : Env Constructor :=
  runUnsafe' do dt.toUnsafe.getConstructor name

@[inherit_doc Dt.getNumConstructors]
def countConstructors : Nat := dt.toUnsafe.getNumConstructors

@[inherit_doc Dt.getConstructorAt]
def getConstructorAt (idx : Fin dt.countConstructors) : Constructor :=
  dt.toUnsafe.getConstructorAt idx

instance : GetElem Datatype Nat Constructor fun dt idx => idx < dt.countConstructors :=
  inferInstanceAs (GetElem Dt Nat DtC fun dt idx => idx < dt.getNumConstructors)

instance [Monad m] : ForIn m Datatype Constructor := inferInstanceAs (ForIn m Dt DtC)

@[inherit_doc Dt.getSelector]
def getSelector (name : String) : Env Selector :=
  runUnsafe' do dt.toUnsafe.getSelector name

@[inherit_doc Dt.getName]
def getName : Res String := dt.toUnsafe.getName

@[inherit_doc Dt.getParameters]
def getParameters : Env (Array Srt) := runUnsafe' do dt.toUnsafe.getParameters

@[inherit_doc Dt.isParametric]
def isParametric : Bool := dt.toUnsafe.isParametric

@[inherit_doc Dt.isCodatatype]
def isCoDatatype : Bool := dt.toUnsafe.isCodatatype

@[inherit_doc Dt.isTuple]
def isTuple : Bool := dt.toUnsafe.isTuple

@[inherit_doc Dt.isRecord]
def isRecord : Bool := dt.toUnsafe.isRecord

@[inherit_doc Dt.isFinite]
def isFinite : Res Bool := dt.toUnsafe.isFinite

@[inherit_doc Dt.isWellFounded]
def isWellFounded : Bool := dt.toUnsafe.isWellFounded

end
