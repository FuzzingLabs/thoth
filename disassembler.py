#!/usr/bin/env python3

import json
from graphviz import Digraph

from function import Function
from utils import format_print, OPERATORS, PRIME
from jsonParser import *

class Disassembler:
   """
   Main class

   loads the cairo json (Bytecode + ABI)
   Analyze and disassemble
   """
   def __init__(self, file, analyze=True):
      self.file = file
      self.functions = []
      self.json = None
      self.call_graph = None
      self.cfg = None

      if analyze:
         self.analyze()

   def _analyze_functions(self):
        """
        Function that creates a function class and return the first function of the linked list
        """
        head = None
        previous = None
        for function in self.json:
            offset_start = list(self.json[function]["instruction"].keys())[0]
            offset_end = list(self.json[function]["instruction"].keys())[-1]
            name = function
            instructions = self.json[function]["instruction"]
            args = self.json[function]["data"]["args"]
            ret = self.json[function]["data"]["return"]
            decorators = self.json[function]["data"]["decorators"]
            functionClass = Function(offset_start, offset_end, name, instructions, args, ret, decorators)
            if (not head):
                head = functionClass
            if (previous):
                previous.nextFunction = functionClass
            previous = functionClass
        return head

   def analyze(self):
      """
      Start the analyze of the code by parsing the cairo/starknet/other json.
      Then it creates every Function class and add it to the Disassembler functions list
      """
      self.json = parseToJson(self.file)
      head_function = self._analyze_functions()
      while (head_function):
         head_function.disassemble_function()
         self.functions.append(head_function)
         head_function = head_function.nextFunction
      return self.functions

   def print(self, func_name=None):
      """
      Iterate over every function and print the disassembly
      """
      if (func_name is None):
         for function in self.functions:
            function.print()
      else:
         function = self.get_function_by_name(func_name)
         if (function != None):
            function.print()
         else:
            print("Error : Function does not exist.")

   def dump_json(self):
      """
      Print the JSON that contains the informations about functions/instructions/opcode ...
      """
      print("\n", json.dumps(self.json, indent=3))

   def get_function_by_name(self, func_name):
      """
      Return a Function if the func_name match
      """
      for function in self.functions:
         if (func_name == function.name):
            return function
      return None

   def get_function_at_offset(self, offset):
      """
      Return a Function if the offset match
      """
      for function in self.functions:
         if (function.offset_start == offset):
            return function
      return None

   def _generate_call_flow_graph_edges(self, dot, function, edgesDone):
      """
      Build the edges of a function
      """
      if (function is None):
         return dot
      if (not function.instruction_data):
         function.instruction_data = function.disassemble_function()
      head_instruction = function.instruction_data
      #dot.node(function.offset_start, function.name)
      while (head_instruction):
         if ("CALL" in head_instruction.opcode):
            offset = int(head_instruction.id) - (PRIME - int(head_instruction.imm))
            if (offset < 0 ):
               offset = int(head_instruction.id) + int(head_instruction.imm)
            if (str(offset) != function.offset_start and (function.offset_start, str(offset)) not in edgesDone):
               edgesDone.append((function.offset_start, str(offset)))
               self._generate_call_flow_graph_edges(dot, self.get_function_at_offset(str(offset)), edgesDone)
               dot.edge(function.offset_start, str(offset))
         head_instruction = head_instruction.nextInstruction
      return dot

   def _generate_call_flow_graph(self):
      """
      Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
      """
      dot = Digraph('CALL FLOW GRAPH', comment='CALL FLOW GRAPH')
      
      # First, we create the nodes
      # TODO - add entrypoint info
      # TODO - add import info
      for function in self.functions:
         dot.node(function.offset_start, function.name)
      edgesDone = []

      # we are creating the edges btw nodes
      for function in self.functions:
         self.call_graph = self._generate_call_flow_graph_edges(dot, function, edgesDone)


   def print_call_flow_graph(self, view=True):
      """
      Print the CallFlowGraph
      """

      # call flow graph not generated yet
      if (self.call_graph == None):
         self._generate_call_flow_graph()

      # show the call flow graph
      self.call_graph.render(directory='doctest-output', view=view)
      return self.call_graph

   def print_cfg(self):
      """
      Print the CFG (Control Flow Graph)
      """

      print("TODO CFG")
      raise NotImplementedError
