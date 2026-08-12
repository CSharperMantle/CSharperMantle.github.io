# -*- coding: utf-8 -*- #
# frozen_string_literal: true

require 'rouge'

module Rouge
  module Lexers
    class GnuAssembler < RegexLexer
      title 'GNU Assembler'
      desc 'Generic GNU as-like assembly syntax'

      tag 'gas'
      aliases 'asm', 'assembly', 'gnu-as'

      state :root do
        rule %r/\/\*/, Comment::Multiline, :block_comment
        rule %r{//[^\r\n]*}, Comment::Single
        rule %r/\#[^\r\n]*/, Comment::Single

        rule %r/[\r\n]+/, Text
        rule %r/[ \t]+/, Text

        # A statement may begin with any number of labels. Keep the label
        # itself plain and highlight only its defining colon.
        rule %r/("(?:\\.|[^"\\\r\n])*"|\d+\$?)([ \t]*)(:)/ do
          groups Text, Text, Punctuation
        end
        rule %r/((?:[A-Za-z_.$][\w.$]*|\\(?:[A-Za-z_.$][\w.$]*|[@+]|\(\)))+)([ \t]*)(:)/ do |m|
          label = m[1]
          offset = 0

          label.to_enum(:scan, %r/\\(?:[A-Za-z_.$][\w.$]*|[@+]|\(\))/).each do
            expansion = Regexp.last_match
            token Text, label[offset...expansion.begin(0)] if expansion.begin(0) > offset
            token Name::Variable, expansion[0]
            offset = expansion.end(0)
          end

          token Text, label[offset..] if offset < label.length
          token Text, m[2]
          token Punctuation, m[3]
        end

        # Symbol assignments occupy the instruction position, but are not
        # instructions themselves.
        rule %r/([A-Za-z_.$][\w.$]*)([ \t]*)(==|=)/ do
          groups Text, Text, Operator
          push :instruction_args
        end

        rule %r/\.[A-Za-z0-9_.$]+/, Keyword, :instruction_args
        rule %r/\\(?:[A-Za-z_.$][\w.$]*|[@+]|\(\))/, Name::Variable, :instruction_args
        rule %r/[A-Za-z_][\w.$]*/, Name::Function, :instruction_args

        # Many GAS targets use semicolons as statement separators.
        rule %r/;/, Punctuation
        rule %r/./, Text
      end

      state :instruction_args do
        rule %r/\\\r?\n/, Str::Escape

        rule %r/\/\*/, Comment::Multiline, :block_comment
        rule %r{//[^\r\n]*}, Comment::Single

        # Prefer an immediate-like reading for an attached hash sign, while a
        # detached hash sign begins a comment.
        rule %r/\#(?=[+\-~]?(?:\d|[A-Za-z_.$(])|:)/, Operator
        rule %r/\#[^\r\n]*/, Comment::Single

        rule %r/"/, Str::Double, :doublequoted
        rule %r/'(?:\\.|[^'\\\r\n])*'/, Str::Single
        rule %r/'(?:\\.|[^\r\n])/, Str::Char

        rule %r/\\(?:[A-Za-z_.$][\w.$]*|[@+]|\(\))/, Name::Variable

        # Numeric local-label references must precede ordinary number rules.
        rule %r/\b\d+[fb]\b/, Name::Label
        rule %r/\b\d+\$(?![\w.$])/, Name::Label

        rule %r/0[xX][0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?[pP][+\-]?\d+/, Num::Float
        rule %r/0[eEfFdDgGhHrRsS][+\-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+\-]?\d+)?/, Num::Float
        rule %r/(?:\d+\.\d*|\.\d+)(?:[eE][+\-]?\d+)?|\d+[eE][+\-]?\d+/, Num::Float
        rule %r/0[xX][0-9a-fA-F]+(?:_[0-9a-fA-F]+)*(?:[uU](?:[lL]{1,2})?|[lL]{1,2}[uU]?)?/, Num::Hex
        rule %r/0[bB][01]+(?:[uU](?:[lL]{1,2})?|[lL]{1,2}[uU]?)?/, Num::Bin
        rule %r/0[0-7]+(?:[uU](?:[lL]{1,2})?|[lL]{1,2}[uU]?)?/, Num::Oct
        rule %r/\d+(?:[uU](?:[lL]{1,2})?|[lL]{1,2}[uU]?)?/, Num::Integer

        mixin :punctuation

        # Operand symbols are intentionally left plain.
        rule %r/[A-Za-z_.$][\w.$]*/, Text
        rule %r/[ \t]+/, Text
        rule %r/;/, Punctuation, :pop!
        rule %r/[\r\n]+/, Text, :pop!
        rule %r/./, Text
      end

      state :punctuation do
        rule %r/<<|>>|==|!=|<>|<=|>=|&&|\|\|/, Operator
        rule %r/[+\-*\/%|&^!~=<>@]/, Operator
        rule %r/[,():\[\]{}]/, Punctuation
      end

      state :doublequoted do
        rule %r/\\\r?\n/, Str::Escape
        rule %r/\\(?:[0-7]{1,3}|[xX][0-9a-fA-F]+|.)/, Str::Escape
        rule %r/"/, Str::Double, :pop!
        rule %r/[^"\\\r\n]+/, Str::Double
        rule %r/[\r\n]+/, Text, :pop!
      end

      state :block_comment do
        rule %r/\*\//, Comment::Multiline, :pop!
        rule %r/[^*]+|\*(?!\/)/, Comment::Multiline
      end
    end
  end
end
