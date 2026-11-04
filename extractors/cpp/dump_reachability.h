#pragma once

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace leancpp {

class DumpReachability {
  enum class Field { other, id, kind, inner };

  struct Frame {
    bool object;
    bool wantsKey;
    bool ast;
    Field field = Field::other;
    std::string id;
    std::string kind;
    bool binary = false;

    Frame(bool isObject, bool onAstPath)
        : object(isObject), wantsKey(isObject), ast(onAstPath) {}
  };

  std::vector<Frame> frames;
  std::unordered_set<std::string> expressions;
  std::unordered_set<std::string> astNodes;
  std::string token;
  bool inString = false;
  bool escaped = false;
  bool usableToken = true;
  bool valid = true;

  void finishString() {
    if (frames.empty() || !frames.back().object)
      return;
    Frame &frame = frames.back();
    if (frame.wantsKey) {
      frame.field = !usableToken ? Field::other
                    : token == "id" ? Field::id
                    : token == "kind" ? Field::kind
                    : token == "inner" ? Field::inner : Field::other;
      frame.wantsKey = false;
    } else {
      if (frame.field == Field::id)
        frame.id = usableToken ? token : std::string();
      if (frame.field == Field::kind) {
        frame.kind = usableToken ? token : std::string();
        frame.binary = usableToken &&
            (token == "BinaryOperator" || token == "CompoundAssignOperator");
      }
      frame.field = Field::other;
    }
  }

public:
  void consume(std::string_view bytes) {
    for (char character : bytes) {
      if (inString) {
        if (escaped) {
          escaped = false;
          usableToken = false;
        } else if (character == '\\') {
          escaped = true;
          usableToken = false;
        } else if (character == '"') {
          finishString();
          inString = false;
        } else if (token.size() < 64) {
          token.push_back(character);
        } else {
          usableToken = false;
        }
        continue;
      }
      if (character == '"') {
        token.clear();
        usableToken = true;
        inString = true;
      } else if (character == '{' || character == '[') {
        const bool ast = frames.empty() ? character == '{' :
            frames.back().ast &&
                (frames.back().object
                     ? frames.back().field == Field::inner && character == '['
                     : character == '{');
        frames.emplace_back(character == '{', ast);
      } else if (character == '}' || character == ']') {
        if (frames.empty() || frames.back().object != (character == '}')) {
          valid = false;
          continue;
        }
        const Frame &frame = frames.back();
        if (frame.object && frame.binary && !frame.id.empty())
          expressions.insert(frame.id);
        if (frame.object && frame.ast && !frame.kind.empty() && !frame.id.empty())
          astNodes.insert(frame.id);
        frames.pop_back();
      } else if (character == ',' && !frames.empty() && frames.back().object) {
        frames.back().wantsKey = true;
      }
    }
  }

  bool complete() const {
    return valid && !inString && frames.empty();
  }

  const std::unordered_set<std::string> &expressionIds() const {
    return expressions;
  }

  // Only the root and `inner` descendants, never referencedDecl/type stubs.
  const std::unordered_set<std::string> &astNodeIds() const {
    return astNodes;
  }
};

}
