module Jekyll
  module StripTopicFilter
    def strip_topic(input)
      return [] if input.nil?
      input.map { |tag| tag.sub(/^[^:]+:/, '') }
    end
  end
end

Liquid::Template.register_filter(Jekyll::StripTopicFilter)
