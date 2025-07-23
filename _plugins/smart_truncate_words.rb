require 'uri'

module Jekyll
  module SmartTruncateWordsFilter
    def smart_truncate_words(input, word_count = 50, max_link_length = 20, truncate_string = '...')
      return input if input.nil? || input.strip.empty?

      text = input.gsub(URI.regexp) do |match|
        link_text = $&.strip
        if link_text.length > max_link_length
          "&lt;link&gt;"
        else
          link_text
        end
      end

      words = []
      current_word = ""
      last_is_cjk = false

      text.each_char do |char|
        if char.match?(/[\p{Ideographic}]/)  # https://docs.ruby-lang.org/en/master/regexp/unicode_properties_rdoc.html
          words << current_word.strip unless current_word.strip.empty?
          words << char
          current_word = ""
          last_is_cjk = true
        elsif char.match?(/\s/)
          words << " " unless last_is_cjk
          words << current_word.strip unless current_word.strip.empty?
          current_word = ""
          last_is_cjk = false
        else
          current_word += char
          last_is_cjk = false
        end
      end
      words << current_word.strip unless current_word.strip.empty?

      non_space_words = words.reject { |w| w.strip.empty? }
      return text if non_space_words.length <= word_count

      result = []
      non_space_count = 0
      words.each do |word|
        if word.strip.empty?
          result << word if non_space_count < word_count
        elsif non_space_count < word_count
          result << word
          non_space_count += 1
        else
          break
        end
      end

      result.join + truncate_string
    end
  end
end

Liquid::Template.register_filter(Jekyll::SmartTruncateWordsFilter)
